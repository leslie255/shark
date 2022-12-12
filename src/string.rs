use std::{
    fmt::{Debug, Display},
    ops::Range,
    slice,
};

/// An immutable string type that allows O(1) indexing using `SourceIndex`.
/// `SourceIndex` can only be obtained by `SourceCharIndices.next`.
/// Doesn't implement `Index` because it requires lifetime of `SourceIndex` to match
/// `SourceString`.
///
/// # Examples
///
/// ```
/// let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");
///
/// let index0 = string.char_indices().skip(8).next().unwrap().0;
/// let index1 = string.char_indices().skip(13).next().unwrap().0;
///
/// assert_eq!(string.get(index0), 'П');
/// assert_eq!(string.slice(index0..index1), "Привет");
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct SourceString {
    raw_string: String,
}

impl SourceString {
    /// Returns an iterator of the character and their indices
    ///
    /// # Examples
    ///
    /// ```
    /// let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");
    /// let mut iter = string.char_indices();
    ///
    /// let (index, char) = iter.next().unwrap();
    /// assert_eq!(string.get(index), Some('你'));
    /// assert_eq!(char, '你');
    ///
    /// let (index, char) = iter.next().unwrap();
    /// assert_eq!(string.get(index), Some('好'));
    /// assert_eq!(char, '好');
    /// ```
    pub fn char_indices<'a>(&'a self) -> SourceCharIndices<'a> {
        SourceCharIndices {
            iter: self.as_bytes().iter(),
            i: 0,
            raw_index: 0,
        }
    }

    /// Returns the character on the index
    ///
    /// # Examples
    ///
    /// ```
    /// let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");
    ///
    /// let index = string.char_indices().skip(8).next().unwrap().0;
    ///
    /// assert_eq!(string.get(index), 'П');
    /// ```
    #[inline]
    pub fn get<'a>(&'a self, index: SourceIndex<'a>) -> Option<char> {
        let bytes = self.as_bytes();
        let bytes = &bytes[index.raw_index..bytes.len() - 1];
        unsafe {
            let (_, char) = next_code_point_indexed(&mut bytes.iter())?;
            Some(char::from_u32_unchecked(char))
        }
    }

    /// Slice the string into a `&str`
    ///
    /// # Panics
    /// Panics if index out of range
    ///
    /// ```
    /// let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");
    ///
    /// let index0 = string.char_indices().skip(8).next().unwrap().0;
    /// let index1 = string.char_indices().skip(13).next().unwrap().0;
    ///
    /// assert_eq!(string.slice(index0..index1), "Привет");
    /// ```
    #[inline]
    pub fn slice<'a>(&'a self, index: Range<SourceIndex<'a>>) -> &'a str {
        let bytes = self
            .as_bytes()
            .get(index.start.raw_index..index.end.raw_index + index.end.len);
        let bytes = match bytes {
            Some(bytes) => bytes,
            None => {
                println!("`SourceString` index out of range when slicing");
                panic!();
            }
        };
        if cfg!(debug) {
            let str = std::str::from_utf8(bytes);
            match str {
                Ok(str) => str,
                Err(e) => {
                    println!("Decode error when slicing `SourceString`:\n{:?}", e);
                    panic!();
                }
            }
        } else {
            unsafe { std::str::from_utf8_unchecked(bytes) }
        }
    }
}

impl From<&'_ str> for SourceString {
    fn from(s: &'_ str) -> Self {
        Self {
            raw_string: s.to_string(),
        }
    }
}

impl From<String> for SourceString {
    fn from(s: String) -> Self {
        Self { raw_string: s }
    }
}

impl Debug for SourceString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.raw_string, f)
    }
}

impl Display for SourceString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.raw_string, f)
    }
}

impl SourceString {
    #[must_use]
    pub fn as_str<'a>(&'a self) -> &'a str {
        self.raw_string.as_str()
    }

    #[must_use]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8] {
        self.raw_string.as_bytes()
    }
}

/// An index pointing to a raw position in the source string
/// **INDEXED PRODUCED FROM ONE SOURCE STRING CAN NEVER BE USED ON ANOTHER SOURCE STRING**
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SourceIndex<'a> {
    raw_index: usize,
    /// length of the character (in bytes)
    len: usize,
    /// The index of the character in the string
    pub position: usize,
    /// `SourceIndex` can't live outside of the `S
    lifetime_lock: &'a (),
}

// https://tools.ietf.org/html/rfc3629
const UTF8_CHAR_WIDTH: [u8; 256] = [
    // 1  2  3  4  5  6  7  8  9  A  B  C  D  E  F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 2
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 3
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 4
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 5
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 6
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 7
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 8
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 9
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // A
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // B
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // C
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // D
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // E
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];

const CONT_MASK: u8 = 0b0011_1111;

/// Given a first byte, determines how many bytes are in this UTF-8 character.
const fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

#[inline]
const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

#[inline]
const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

/// Modified from `std::str::next_code_point`
/// Returns the length of the character, and the next code point in UTF-8
unsafe fn next_code_point_indexed<'a, I: Iterator<Item = &'a u8>>(
    bytes: &mut I,
) -> Option<(usize, u32)> {
    // Decode UTF-8
    let x = *bytes.next()?;
    if x < 128 {
        return Some((1, x as u32));
    }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);
    // SAFETY: `bytes` produces an UTF-8-like string,
    // so the iterator must produce a value here.
    let y = *bytes.next().unwrap_unchecked();
    let mut increments = 2usize;
    let mut ch = utf8_acc_cont_byte(init, y);
    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        // SAFETY: `bytes` produces an UTF-8-like string,
        // so the iterator must produce a value here.
        let z = *bytes.next().unwrap_unchecked();
        increments = 3;
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, z);
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            // SAFETY: `bytes` produces an UTF-8-like string,
            // so the iterator must produce a value here.
            let w = *bytes.next().unwrap_unchecked();
            increments = 4;
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z, w);
        }
    }

    Some((increments, ch))
}

#[derive(Clone)]
pub struct SourceCharIndices<'a> {
    iter: slice::Iter<'a, u8>,
    i: usize,
    raw_index: usize,
}

impl<'a> Iterator for SourceCharIndices<'a> {
    type Item = (SourceIndex<'a>, char);

    fn next(&mut self) -> Option<(SourceIndex<'a>, char)> {
        unsafe {
            let (len, ch) = next_code_point_indexed(&mut self.iter)?;
            let raw_index = self.raw_index;
            self.raw_index += len;
            let position = self.i;
            self.i += 1;
            let ch = char::from_u32_unchecked(ch);

            Some((
                SourceIndex {
                    raw_index,
                    len,
                    position,
                    lifetime_lock: &(),
                },
                ch,
            ))
        }
    }
}
