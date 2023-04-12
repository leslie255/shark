use std::{cell::RefCell, collections::HashMap, fmt::Debug, fs, ops::Deref};

use crate::string::SourceString;

/// Owns contents of already opened files to avoid re-reading files when a file is included
/// multiple times
/// - Also owns all of the identifier names (as slices of the source string)
/// - Does not own the path strings
#[derive(Default)]
pub struct BufferedContent {
    map: RefCell<HashMap<&'static str, SourceString>>,
}
impl BufferedContent {
    /// If the file hasn't been opened before, read it from the disk and buffer it
    /// Otherwise returns the previously buffered string
    pub fn read_file(&self, path: &'static str) -> SourceString {
        if let Some(&cached_content) = self.map.borrow().get(path) {
            return cached_content;
        }
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => panic!("Unable to open file {:?}: {:?}", path, e),
        };
        let source = SourceString::from(String::leak(source) as &'static str);
        self.map.borrow_mut().insert(path, source);
        source
    }
}
impl Debug for BufferedContent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.map.try_borrow() {
            Ok(map) => map.deref().fmt(f),
            Err(_) => write!(f, "[BufferedContent is being mut borrowed somewhere else]"),
        }
    }
}
