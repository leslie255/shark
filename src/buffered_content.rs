use std::{
    cell::{RefCell, UnsafeCell},
    collections::HashMap,
    fmt::Debug,
    fs,
};

use crate::string::SourceString;

/// Owns contents of already opened files to avoid re-reading files when a file is included
/// multiple times
/// - Also owns all of the identifier names (as slices of the source string)
/// - Does not own the path strings
#[derive(Default)]
pub struct BufferedContent<'src> {
    /// Uses `UnsafeCell` internally because when a source string is stored in the map it is never
    /// dropped or changed, so returning a reference of it is always safe
    ///
    /// (It may look like that all already existing references will be invalid when the `HashMap`
    /// is reallocated, and therefore causeing segment fault, but since the struct never gives out
    /// a reference to the `SourceString`, but rather the inner `&'src str` inside the `String`, it
    /// would not matter if the `SourceString` is reallocated as long as the inner `str` is not
    /// changed)
    ///
    /// Uses internal mutability because this struct is borrowed by the both the main compiler and
    /// the error collector, and it cannot be `mut` borrowed multiple times,
    ///
    /// Also, for all that the outside world is concerned, whether or not `read_file` reads from
    /// the disk or from the buffered string would not matter, so they shouldn't worry about `mut`
    map: RefCell<HashMap<&'src str, UnsafeCell<SourceString>>>,
}
impl<'src> BufferedContent<'src> {
    /// If the file hasn't been opened before, read it from the disk and buffer it
    /// Otherwise returns the previously buffered string
    pub fn read_file(&'src self, path: &'src str) -> &'src SourceString {
        if let Some(cached_content) = self.map.borrow().get(path) {
            return unsafe { cached_content.get().as_ref().unwrap() };
        }
        let string = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => panic!("Unable to open file {:?}: {:?}", path, e),
        };
        self.map
            .borrow_mut()
            .insert(path, UnsafeCell::new(string.into()));
        unsafe { self.map.borrow().get(path).unwrap().get().as_ref().unwrap() }
    }
}
impl Debug for BufferedContent<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BufferedContent ")?;
        f.debug_map()
            .entries(
                self.map
                    .borrow()
                    .iter()
                    .map(|(path, str)| (path, unsafe { str.get().as_ref().unwrap() })),
            )
            .finish()
    }
}
