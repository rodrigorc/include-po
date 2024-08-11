use std::io::{BufRead, Write};
use std::path::Path;
use thiserror::Error;

mod plurals;

#[derive(Error, Debug)]
pub enum PoIncludeError {
    #[error(transparent)]
    Io { #[from] source: std::io::Error },
}

pub type Result<T> = std::result::Result<T, PoIncludeError>;

pub fn generate_locales_from_dir(po_dir: impl AsRef<Path>, out_path: impl AsRef<Path>) -> Result<()> {
    let po_dir = po_dir.as_ref();
    let out_path = out_path.as_ref();
    let out_dir = out_path.parent().expect("No directory in output path");
    if !out_dir.is_dir() {
        std::fs::create_dir_all(out_dir)?;
    }

    let out = std::fs::File::create(out_path)?;
    let mut out = std::io::BufWriter::new(out);
    writeln!(out, r#"#[path = "{}"]"#, std::path::absolute(out_dir).unwrap().display())?;
    writeln!(out, r#"
#[allow(unused_variables)]
pub mod translators {{
"#)?;

    let mut objs = Vec::new();
    for entry in po_dir.read_dir()? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("po") {
            continue;
        }
        let Some(lang) = path.file_stem() else { continue };
        let lang = lang.to_ascii_lowercase();
        let lang = lang.to_str().unwrap().to_owned();
        generate_rs_from_po(path, out_dir.join(&format!("{lang}.rs")))?;
        println!("cargo:rerun-if-changed={}", entry.path().display());

        writeln!(out, "pub mod {lang};")?;
        objs.push(lang);
    }

    write!(out, r#"
use std::borrow::Cow;

pub fn set_locale(name: &str) -> bool {{
    let name = name.to_ascii_lowercase();
    if set_locale_inner(&name) {{
        return true;
    }}
    if let Some(p) = name.find('_').or_else(|| name.find('-')) {{
        let (base, _) = name.split_at(p);
        if set_locale_inner(base) {{
            return true;
        }}
    }}
    ::tr::set_translator!(NullTranslator);
    false
}}

fn set_locale_inner(name: &str) -> bool {{
    match name {{
"#)?;
    for lang in &objs {
        writeln!(out, r#"        "{lang}" => ::tr::set_translator!({lang}::Translator),"#)?;
    }
    write!(out, r#"
        _ => return false,
    }}
    true
}}

pub struct NullTranslator;

impl ::tr::Translator for NullTranslator {{
    fn translate<'a>(&'a self, string: &'a str, _context: Option<&'a str>) -> Cow<'a, str> {{
        Cow::Borrowed(string)
    }}
    fn ntranslate<'a>(&'a self, n: u64, singular: &'a str, plural: &'a str, _context: Option<&'a str>) -> Cow<'a, str> {{
        if n == 1 {{ Cow::Borrowed(singular) }} else {{ Cow::Borrowed(plural) }}
    }}
}}
"#)?;
    writeln!(out, "}}")?;
    Ok(())
}

#[derive(Debug)]
pub struct Message {
    pub context: Option<String>,
    pub id: String,
    pub text: String,
}

#[derive(Debug)]
pub struct PMessage {
    pub context: Option<String>,
    pub singular: String,
    pub plural: String,
    pub texts: Vec<String>,
}

pub fn parse_po(po_path: impl AsRef<Path>) -> Result<(Vec<Message>, Vec<PMessage>)> {
    let f = std::fs::File::open(po_path)?;
    let f = std::io::BufReader::new(f);
    let mut text = String::new();
    let mut last_key: Option<String> = None;
    let mut id: Option<String> = None;
    let mut id_plural: Option<String> = None;
    let mut msgs: Vec<String> = Vec::new();
    let mut ctxt: Option<String> = None;

    let mut messages = Vec::new();
    let mut pmessages = Vec::new();

    // Ensure an empty string to flush the last message
    for line in f.lines().chain([Ok(String::new())]) {
        let line = line?;
        let line = line.trim_ascii();
        let head = line.chars().next();

        match head {
            Some('#') => {
                continue;
            }
            Some('"') => {
                text.push_str(&unquote(line));
                continue;
            }
            _ => {
                match last_key.take().as_deref() {
                    None => (),
                    Some("msgid") => id = Some(std::mem::take(&mut text)),
                    Some("msgid_plural") => id_plural = Some(std::mem::take(&mut text)),
                    Some("msgstr") => msgs = vec![std::mem::take(&mut text)],
                    Some("msgctxt") => ctxt = Some(std::mem::take(&mut text)),
                    Some(unk) if unk.starts_with("msgstr[") => msgs.push(std::mem::take(&mut text)),
                    Some(_) => { }
                }
            }
        }

        let (next_key, sub_text) = match line.find(' ') {
            Some(p) => {
                let (a, b) = line.split_at(p);
                let (_, b) = b.split_at(1);
                (a, unquote(b))
            }
            None => (line, ""),
        };

        // start of next entry or separator or end of file
        if next_key.is_empty() || next_key == "msgid" {
            let mut msgs = std::mem::take(&mut msgs);
            if msgs.len() > 0 {
                match (id.take(), id_plural.take(), ) {
                    (Some(id), None) => {
                        messages.push(Message {
                            context: ctxt.take(),
                            id,
                            text: std::mem::take(&mut msgs[0]),
                        });
                    }
                    (Some(singular), Some(plural)) => {
                        pmessages.push(PMessage {
                            context: ctxt.take(),
                            singular,
                            plural,
                            texts: msgs,
                        });
                    }
                    _ => {}
                }
            }
        }

        if !next_key.is_empty() {
            last_key = Some(String::from(next_key));
            text = String::from(sub_text);
        }
    }
    Ok((messages, pmessages))
}

pub fn generate_rs_from_po(po_path: impl AsRef<Path>, out_path: impl AsRef<Path>) -> Result<()> {
    use std::collections::BTreeMap;

    let (messages, pmessages) = parse_po(po_path)?;


    let mut plural_count: usize = 2;
    let mut plural_expr = plurals::Expr::default();
    let descr = &messages.iter().find(|m| m.id.is_empty()).as_ref().unwrap().text;
    // The description looks like HTML headers
    for header in descr.split("\\n") {
        let Some(colon) = header.find(':') else { continue };
        let name = header[.. colon].trim();
        let value = header[colon + 1 ..].trim();
        match name.to_lowercase().as_str() {
            "content-type" => {
                if value.contains("charset=") && !value.contains("=UTF-8") {
                    panic!("Only UTF-8 po files, please");
                }
            }
            "plural-forms" => {
                let values: Vec<_> = value.split(";").collect();
                plural_count = values[0].split("=").collect::<Vec<_>>()[1].parse().unwrap();

                let str_plural = values[1];
                let eq = str_plural.find('=').unwrap();
                let str_plural = str_plural[eq + 1 ..].trim();
                plural_expr = plurals::Expr::parse(str_plural).unwrap();
            }
            _ => {}
        }
    }

    let mut messages_by_ctx = BTreeMap::<Option<&str>, Vec<&Message>>::new();
    for msg in &messages {
        if msg.id.is_empty() || msg.text.is_empty() {
            continue;
        }
        let entry = messages_by_ctx.entry(msg.context.as_deref());
        entry.or_default().push(msg);
    }
    let mut pmessages_by_ctx = BTreeMap::<Option<&str>, Vec<&PMessage>>::new();
    for pmsg in &pmessages {
        if pmsg.singular.is_empty() || pmsg.texts.is_empty() || pmsg.texts[0].is_empty() {
            continue;
        }
        let entry = pmessages_by_ctx.entry(pmsg.context.as_deref());
        entry.or_default().push(pmsg);
    }

    let out = std::fs::File::create(out_path)?;
    let mut out = std::io::BufWriter::new(out);

    write!(out,
r#"
#![allow(dead_code, text_direction_codepoint_in_literal)]

use std::borrow::Cow;
pub struct Translator;

pub const PLURALS: usize = {plural_count};

#[allow(unused_parens)]
pub fn number_index(n: u64) -> u32 {{
    {plural_expr}
}}

impl ::tr::Translator for Translator {{
    fn translate<'a>(&'a self, string: &'a str, context: Option<&'a str>) -> Cow<'a, str> {{
        let s = match context {{
"#)?;

    for (ctxt, messages) in &messages_by_ctx {
        let s;
        writeln!(out, r#"            {} => match string {{"#,
            match &ctxt {
                None => "None",
                Some(x) => { s = format!(r#"Some("{}")"#, x); &s }
            }
        )?;

        for msg in messages {
            writeln!(out, r#"                "{}" => "{}","#,
                msg.id,
                msg.text,
            )?;
        }
        writeln!(out, r#"                _ => string,
            }},"#)?;
    }
    write!(out,
r#"
            _ => string,
        }};
        Cow::Borrowed(s)
    }}
    fn ntranslate<'a>(&'a self, n: u64, singular: &'a str, plural: &'a str, context: Option<&'a str>) -> Cow<'a, str> {{
        let ni = number_index(n);
        let s = match context {{
"#)?;
    for (ctxt, pmessages) in &pmessages_by_ctx {
        let s;
        writeln!(out, r#"            {} => match singular {{"#,
            match &ctxt {
                None => "None",
                Some(x) => { s = format!(r#"Some("{}")"#, x); &s }
            }
        )?;
        for pmsg in pmessages {
            write!(out, r#"                "{}" => {{ match ni {{ "#,
                pmsg.singular,
            )?;
            // skip the 0 because it is the default, avoid the duplicate
            for (i, m) in pmsg.texts.iter().enumerate().take(plural_count).skip(1) {
                write!(out, r#"{} => "{}", "#, i, m)?;
            }
            writeln!(out, r#"_ => "{}" }} }}"#, pmsg.texts[0])?;
        }
        writeln!(out, r#"                _ => if n == 1 {{ singular }} else {{ plural }},
            }},"#)?;
    }
    write!(out,
r#"
            _ => if n == 1 {{ singular }} else {{ plural }},
        }};
        Cow::Borrowed(s)
    }}
}}
"#)?;

    Ok(())
}

fn unquote(line: &str) -> &str {
    // Remove the starting and ending quotes
    let (_, line) = line.split_at(1);
    let (line, _) = line.split_at(line.len() - 1);
    // po quoting is similar enough to Rust's so nothing else to do
    line
}

