use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::ast::type_expr::TypeExpr;
use crate::ast::FnSignature;

/// Some expression can have multiple possible types, this type keeps track of these types and can
/// determine whether or not a type expression is one of the possible types
#[derive(Debug, Clone)]
pub enum PossibleTypes<'src> {
    IntNumeric,         // u64, u32, u16, u8, i64, i32, i16, i8, f64, f32,
    NegativeIntNumeric, // i64, i32, i16, i8, f64, f32,
    FloatNumeric,       // f64, f32
    Known(TypeExpr<'src>),
}

impl<'src> PossibleTypes<'src> {
    /// Suggest a default type from all the possible types
    pub fn default_type(self) -> TypeExpr<'src> {
        match self {
            PossibleTypes::IntNumeric => TypeExpr::I32,
            PossibleTypes::NegativeIntNumeric => TypeExpr::I32,
            PossibleTypes::FloatNumeric => TypeExpr::F64,
            PossibleTypes::Known(t) => t.clone(),
        }
    }

    /// Returns whether or not a type is included in all possible types
    pub fn matches_types(&self, t: &TypeExpr, symbol_table: &SymbolTable<'src>) -> bool {
        match self {
            PossibleTypes::IntNumeric => t.is_numeric(symbol_table),
            PossibleTypes::NegativeIntNumeric => t.is_signed_numeric(symbol_table),
            PossibleTypes::FloatNumeric => t.is_float_numeric(symbol_table),
            PossibleTypes::Known(t0) => TypeExpr::eq(t0, t, symbol_table),
        }
    }
}

#[derive(Debug, Clone)]
pub enum SymbolType<'src> {
    Var( PossibleTypes<'src>),
    Fn(FnSignature<'src>),
    // type names are stored separately (there are no local type names)
}

impl<'src> SymbolType<'src> {
    pub fn as_var(&self) -> Option<&PossibleTypes<'src>> {
        if let Self::Var(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_fn(&self) -> Option<&FnSignature<'src>> {
        if let Self::Fn(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
/// The symbol table is stored as a stack, every time the parser enters a block, a new set of
/// symbols is pushed onto the stack containing the symbols in that block
pub struct SymbolTable<'src> {
    typenames: HashMap<&'src str, TypeExpr<'src>>,
    symbols: Vec<HashMap<&'src str, SymbolType<'src>>>,
}

impl Default for SymbolTable<'_> {
    /// Generates a `SymbolTable` with only one empty layer
    #[inline]
    fn default() -> Self {
        Self {
            typenames: HashMap::default(),
            symbols: vec![HashMap::new()],
        }
    }
}

impl<'s> SymbolTable<'s> {
    /// Returns the type of the variable with the given name.
    ///
    /// # Arguments
    ///
    /// * `var_name` - The name of the variable
    ///
    /// # Returns
    ///
    /// If a variable with the given name exists in the symbol table, returns a reference to a
    /// `PossibleTypes` enum representing the possible types of the variable.
    /// Otherwise (if no variable with the given name exists), returns `None`.
    pub fn var_type(&self, var_name: &'s str) -> Option<&PossibleTypes<'s>> {
        self.symbols
            .iter()
            .rev()
            .find_map(|symbols| symbols.get(var_name))?
            .as_var()
    }

    /// Returns the signature of the function with the given name, if it exists.
    ///
    /// # Arguments
    ///
    /// * `fn_name` - The name of the function
    ///
    /// # Returns
    ///
    /// If a function with the given name exists, returns a reference to its signature.
    /// Otherwise, returns `None`.
    pub fn fn_signature(&self, fn_name: &'s str) -> Option<&FnSignature<'s>> {
        self.symbols
            .iter()
            .rev()
            .find_map(|symbols| symbols.get(fn_name))?
            .as_fn()
    }

    /// Returns the type of a typename
    ///
    /// # Arguments
    ///
    /// * `typename` - The typename
    ///
    /// # Returns
    ///
    /// If a type with the given name exists, returns a reference to that type
    /// Otherwise, returns `None`.
    pub fn typename(&self, typename: &'s str) -> Option<&TypeExpr<'s>> {
        self.typenames.get(typename)
    }

    /// The symbol table is stored as a stack, when the type checker enters a block, a new empty
    /// layer is pushed onto the stack
    pub fn push_layer(&mut self) {
        self.symbols.push(HashMap::default());
    }

    /// The symbol table is stored as a stack, when the type checker leaves a block, a new empty
    /// layer is popped off the stack
    pub fn pop_layer(&mut self) {
        self.symbols.pop();
    }

    /// Adds a new variable with the given name and possible types to the top symbol table layer.
    /// If the variable already exists, override it (on the top level).
    ///
    /// # Arguments
    ///
    /// * `var_name` - A string slice containing the name of the variable to add.
    /// * `id` - The ID for that variable
    /// * `possible_types` - A `PossibleTypes` enum representing the possible types of the variable.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut symbols = SymbolTable::default();
    /// symbols.push_layer();
    /// symbols.add_var("x", PossibleTypes::IntNumeric);
    /// ```
    pub fn add_var(&mut self, var_name: &'s str, possible_types: PossibleTypes<'s>) {
        self.symbols
            .last_mut()
            .expect("Adding a variable to an empty stack")
            .insert(var_name, SymbolType::Var(possible_types));
    }

    /// Adds a new function with the given name and signature to the top symbol table layer.
    /// Will not add the function if it already exists on the top layer.
    /// Returns whether or not the function already exists
    ///
    /// # Arguments
    ///
    /// * `fn_name` - A string slice containing the name of the variable to add.
    /// * `fn_signature` - The signature of that function
    ///
    /// # Examples
    ///
    /// ```
    /// let mut symbols = SymbolTable::default();
    /// let fn_exists = symbols.add_fn(
    ///     "main",
    ///     FnSignature {
    ///         args: Vec::new(),
    ///         ret_type: Some(TypeExprNode::I32.wrap()),
    ///     },
    /// );
    /// assert_eq!(fn_exists, false);
    /// let fn_exists = symbols.add_fn(
    ///     "main",
    ///     FnSignature {
    ///         args: Vec::new(),
    ///         ret_type: Some(TypeExprNode::I32.wrap()),
    ///     },
    /// );
    /// assert_eq!(fn_exists, true);
    /// ```
    pub fn add_fn(&mut self, fn_name: &'s str, fn_signature: FnSignature<'s>) -> bool {
        let top_layer = self
            .symbols
            .last_mut()
            .expect("Adding a variable to an empty stack");
        match top_layer.entry(fn_name) {
            Entry::Occupied(_) => true,
            Entry::Vacant(v) => {
                _ = v.insert(SymbolType::Fn(fn_signature));
                false
            }
        }
    }

    /// Adds a type name to the symbol table.
    ///
    /// # Arguments
    /// * `typename` - The name of the type.
    /// * `dtype` - The type expression of the type.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut symbols = SymbolTable::default();
    /// symbols.add_typename("Byte", TypeExprNode::U8.wrap());
    /// ```
    pub fn add_typename(&mut self, typename: &'s str, dtype: TypeExpr<'s>) {
        self.typenames.insert(typename, dtype);
    }
}
