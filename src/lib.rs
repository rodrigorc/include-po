//! This crate contains functions to parse PO files (gettext message catalogs) and use them in Rust.
//!
//! # Main usage
//!
//! The recommended use is to use it to build a Rust module with the translations.
//!
//! First build your PO files into the `locales` directory, in the root of your project.
//!
//! Then this the crate as a `[build-dependencies]` and `tr` as a normal one: in your `Cargo.toml`:
//! ```
//! [dev-dependencies]
//! include-po = "0.1"
//!
//! [dependencies]
//! tr = { version = "0.1.10", default-features = false }
//! ```
//! Write a `build.rs` script:
//! ```
//! fn main() {
//!     let output_dir = std::env::var("OUT_DIR").unwrap();
//!     let out = std::path::PathBuf::from(&output_dir).join("locale/translators.rs");
//!     include_po::generate_locales_from_dir("locales", out).unwrap();
//! }
//! ```
//! And finally in your `main.rs` or `lib.rs`:
//! ```
//! include!(concat!(env!("OUT_DIR"), "/locale/translators.rs"));
//! ```
//! That's it! Now you can call `translators::set_locale("es");` to switch to Spanish!
//!
//! If you are writing a lib crate, as a convention you should have a public function in the root namespace:
//! ```
//! fn set_locale(locale: &str) {
//!     translators::set_locale(locale);
//! }
//! ```
//! This way you can chain the locale of multiple translatable libraries.
//!
//! # Other functions
//!
//! If you prefer to do the translations yourself, you can also use this crate to parse the PO file and obtain
//! the messages. But note that currently the messages will be unescaped, that is a '"' will be a '\n' and so on.
//!
//! # Why PO instead of MO?
//!
//! Most solutions based on gettext read the message catalog from the MO file, instead of the PO. A MO file is a
//! compiled message catalog. The reason original gettext uses MO files is to optimize start-up time: when the
//! `gettext` library wants to use a MO, it just locates the file, opens it and memory-maps it. It does very little
//! parse, because everything is designed to be used from that memory map. It even contains a precomputed hash table!
//!
//! In Rust, I see little reason to distribute MO files separated from the executable. Some people try to use `include_bytes!`
//! and then parse the binary data into a `BTreeMap`... but that defeats the purpose of the MO existence in the first place.
//!
//! If you are going to embed the message catalog into the executable you may as well go all the way and include it as code:
//! once again the catalog is memory mapped (as it is most executable code) and with zero parsing at runtime. But if you are
//! going to parse the catalog and convert it to Rust at build time, why read the MO and not the PO that is simpler and saves
//! a compiler step?
//!
//! But what about the hash table? you are probably asking... Well, currently this crate is building a giant `match string`
//! for each source PO file. This seems to be good enough, but if needed we can transparently upgrade it to a cleverer algoritm.
//! My hope is that the code generated by the compiler will get better faster than the needs of this crate.

#![allow(clippy::needless_doctest_main)]

use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use thiserror::Error;

mod plurals;

/// An error while parsing or processing a PO file.
#[derive(Error, Debug)]
pub enum PoIncludeError {
    #[error("Invalid path '{0}'")]
    InvalidPath(PathBuf),
    #[error("Non-UTF-8 PO file '{0}'")]
    NonUtf8PoFile(PathBuf),
    #[error("Invalid plural expression")]
    PluralError,
    #[error(transparent)]
    Io { #[from] source: std::io::Error },
}

/// The default return type.
pub type Result<T> = std::result::Result<T, PoIncludeError>;

/// Build a module with all the translations from a directory.
///
/// This function creates a module `translators` in the given directory. Then,
/// for each PO file in the source directory it will create a submodule.
/// Then, in the root module it creates a function `set_locale(locale: &str)` that
/// chooses the given locale by calling the `tr::set_translator()`.
pub fn generate_locales_from_dir(po_dir: impl AsRef<Path>, out_path: impl AsRef<Path>) -> Result<()> {
    let po_dir = po_dir.as_ref();
    let out_path = out_path.as_ref();
    let out_dir = out_path.parent().ok_or_else(|| PoIncludeError::InvalidPath(out_path.to_owned()))?;
    if !out_dir.is_dir() {
        std::fs::create_dir_all(out_dir)?;
    }

    let out = std::fs::File::create(out_path)?;
    let mut out = std::io::BufWriter::new(out);
    let mod_path = std::path::absolute(out_dir)?;
    writeln!(out, r#"#[path = "{}"]"#, mod_path.display())?;
    writeln!(out, r#"#[allow(unused_variables)]
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
        let Some(lang) = lang.to_str() else { continue };
        let lang = lang.to_owned();
        generate_rs_from_po(path, out_dir.join(format!("{lang}.rs")))?;
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

/// A simple message from the PO file.
#[derive(Debug)]
pub struct Message {
    pub context: Option<String>,
    pub id: String,
    pub text: String,
}

/// A message with plural form.
#[derive(Debug)]
pub struct PMessage {
    pub context: Option<String>,
    pub singular: String,
    pub plural: String,
    pub texts: Vec<String>,
}

/// Parses a PO file.
///
/// Returns the normal and the pluralized messages in two separated vectors.
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
                text.push_str(unquote(line));
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
            if !msgs.is_empty() {
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

fn split_at_char(s: &str, c: char) -> Option<(&str, &str)> {
    let pos = s.find(c)?;
    let a = s[.. pos].trim();
    let b = s[pos + c.len_utf8() ..].trim();
    Some((a, b))
}

fn unquote(line: &str) -> &str {
    // Remove the starting and ending quotes
    let (_, line) = line.split_at(1);
    let (line, _) = line.split_at(line.len() - 1);
    // po quoting is similar enough to Rust's so nothing else to do
    line
}

/// Converts a PO file to the corresponding Rust source module.
pub fn generate_rs_from_po(po_path: impl AsRef<Path>, out_path: impl AsRef<Path>) -> Result<()> {
    use std::collections::BTreeMap;

    let po_path = po_path.as_ref();
    let (messages, pmessages) = parse_po(po_path)?;


    let mut plural_count: usize = 2;
    let mut plural_expr = plurals::Expr::default();
    // The empty string is translated as the "description", that looks HTML headers
    if let Some(descr) = messages.iter().find(|m| m.id.is_empty()).as_ref().map(|m| m.text.as_str()) {
        // TODO: maybe we should unescape the text, but it doesn't seem to be too necessary
        for header in descr.split("\\n") {
            let Some((name, value)) = split_at_char(header, ':') else { continue };
            match name.to_lowercase().as_str() {
                "content-type" => {
                    for field in value.split(';') {
                        let Some((n, v)) = split_at_char(field, '=') else { continue };
                        if n == "charset" && v != "UTF-8" && v != "ASCII" {
                            return Err(PoIncludeError::NonUtf8PoFile(po_path.to_owned()));
                        }
                    }
                }
                "plural-forms" => {
                    for field in value.split(';') {
                        let Some((n, v)) = split_at_char(field, '=') else { continue };
                        match n {
                            "nplurals" => {
                                plural_count = v.parse().map_err(|_| PoIncludeError::PluralError)?;
                            }
                            "plural" => {
                                plural_expr = plurals::Expr::parse(v).map_err(|_| PoIncludeError::PluralError)?;
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
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
#![allow(dead_code)]

use std::borrow::Cow;
pub struct Translator;

pub const PLURALS: usize = {plural_count};

#[allow(unused_parens)]
pub fn number_index(n: u64) -> u32 {{
    {plural_expr}
}}

#[allow(clippy::match_single_binding)]
impl ::tr::Translator for Translator {{
    fn translate<'a>(&'a self, string: &'a str, context: Option<&'a str>) -> Cow<'a, str> {{
        let s = match context {{
"#)?;

    for (ctxt, messages) in &messages_by_ctx {
        let s;
        writeln!(out, r#"            {} => match string {{"#,
            match &ctxt {
                None => "None",
                Some(x) => { s = format!(r#"Some("{x}")"#); &s }
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
                Some(x) => { s = format!(r#"Some("{x}")"#); &s }
            }
        )?;
        for pmsg in pmessages {
            write!(out, r#"                "{}" => {{ match ni {{ "#,
                pmsg.singular,
            )?;
            // skip the 0 because it is the default, avoid the duplicate
            for (i, m) in pmsg.texts.iter().enumerate().take(plural_count).skip(1) {
                write!(out, r#"{i} => "{m}", "#)?;
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

