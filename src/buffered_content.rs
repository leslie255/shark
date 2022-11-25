use std::{
    cell::{RefCell, UnsafeCell},
    collections::HashMap,
    fs,
};

/// Owns contents of already opened files to avoid re-reading files when a file is included
/// multiple times
/// - Also owns all of the identifier names (as slices of the source string)
/// - Does not own the path strings
#[derive(Debug, Default)]
pub struct BufferedContent<'a> {
    // Uses unsafe because when a source string is stored in the map it is never dropped or
    // changed, so returning a reference from it is always safe
    map: RefCell<HashMap<&'a str, UnsafeCell<String>>>,
}
impl<'a> BufferedContent<'a> {
    /// If the file is previously opened, return the cached content, otherwise
    /// Otherwise open the file, add it into the buffer, and then return the content
    pub fn open_file(&'a self, path: &'a str) -> &str {
        if let Some(cached_content) = self.map.borrow().get(path) {
            return unsafe { cached_content.get().as_ref().unwrap() };
        }
        let string = fs::read_to_string(path).expect("Unable to read file");
        self.map.borrow_mut().insert(path, string.into());
        unsafe { self.map.borrow().get(path).unwrap().get().as_ref().unwrap() }
    }
}
