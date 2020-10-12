package maf.language.scheme.lattices

object SchemeOps {

  /** These are the unary operations that should be supported by Scheme lattices */
  object UnaryOperator extends Enumeration {
    val
    IsNull, IsBoolean, IsCons, IsPointer, IsChar, IsSymbol, IsString, IsInteger, IsReal, IsVector, IsThread, IsLock, IsProcedure, /* Check the type of a value */
    Not, /* Negate a value */
    Ceiling, Floor, Round, Random, Sqrt, /* Unary arithmetic operations */
    Sin, ASin, Cos, ACos, Tan, ATan, Log, /* Transcendental functions */
    VectorLength, StringLength, /* Length operations */
    NumberToString, SymbolToString, StringToSymbol, StringToNumber, IntegerToCharacter,  /* Conversions */
    ExactToInexact, InexactToExact, CharacterToInteger, CharacterToString,
    CharacterDowncase, CharacterUpcase, CharacterIsLower, CharacterIsUpper = Value
  }
  type UnaryOperator = UnaryOperator.Value

  /** Binary operations that should be supported by lattices */
  object BinaryOperator extends Enumeration {
    val
    Plus, Minus, Times, Div, Quotient, Modulo, Remainder, Expt, /* Arithmetic operations */
    Lt, /* Arithmetic comparison */
    /* Equality checking */
    NumEq, /* number equality */
    Eq, /* physical equality */
    StringAppend, StringRef, StringLt, /* String operations */
    CharacterEq, CharacterLt, CharacterEqCI, CharacterLtCI /* Characters */ = Value
  }
  type BinaryOperator = BinaryOperator.Value
}
