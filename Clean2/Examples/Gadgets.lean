/-
The gadgets of `Clean2/Gadgets`, instantiated on the expression backend and on R1CS.
-/
module

public import Clean2.Gadgets.Bool
public import Clean2.Gadgets.Gates
public import Clean2.Gadgets.IsZero
public import Clean2.Gadgets.Equality
public import Clean2.Gadgets.Inverse
public import Clean2.Gadgets.Select
public import Clean2.Gadgets.Bits2Num

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native] [DecidableEq Native]

/-! ## Booleans -/

def assertBoolExpr : Impl (ExprBackend Native) AssertBool.interface := AssertBool.impl ExprBackend.mulEq
def assertBoolR1CS : Impl (R1CS Native) AssertBool.interface := AssertBool.impl R1CS.mulEq

def toBitExpr : Impl (ExprBackend Native) ToBit.interface := ToBit.impl assertBoolExpr
def toBitR1CS : Impl (R1CS Native) ToBit.interface := ToBit.impl assertBoolR1CS

def xorExpr : Impl (ExprBackend Native) (Xor.interface (bit Native)) := Xor.impl ExprBackend.arith
def xorR1CS : Impl (R1CS Native) (Xor.interface (bit Native)) := Xor.impl R1CS.arith

def xor3R1CS : Impl (R1CS Native) (Xor3.interface (bit Native)) := Xor3.impl xorR1CS
def xor3Expr : Impl (ExprBackend Native) (Xor3.interface (bit Native)) := Xor3.impl xorExpr

/-! ## Gates -/

section
open Gates

def notExpr : Impl (ExprBackend Native) (NOT.interface (bit Native)) := NOT.impl ExprBackend.arith
def andExpr : Impl (ExprBackend Native) (AND.interface (bit Native)) := AND.impl ExprBackend.arith
def orExpr : Impl (ExprBackend Native) (OR.interface (bit Native)) := OR.impl ExprBackend.arith
def nandExpr : Impl (ExprBackend Native) (NAND.interface (bit Native)) := NAND.impl andExpr notExpr
def norExpr : Impl (ExprBackend Native) (NOR.interface (bit Native)) := NOR.impl orExpr notExpr

def notR1CS : Impl (R1CS Native) (NOT.interface (bit Native)) := NOT.impl R1CS.arith
def andR1CS : Impl (R1CS Native) (AND.interface (bit Native)) := AND.impl R1CS.arith
def orR1CS : Impl (R1CS Native) (OR.interface (bit Native)) := OR.impl R1CS.arith
def nandR1CS : Impl (R1CS Native) (NAND.interface (bit Native)) := NAND.impl andR1CS notR1CS
def norR1CS : Impl (R1CS Native) (NOR.interface (bit Native)) := NOR.impl orR1CS notR1CS

end

/-! ## Zero tests and equality -/

def isZeroExpr : Impl (ExprBackend Native) (IsZero.interface (bit Native)) := IsZero.impl ExprBackend.arith
def isZeroR1CS : Impl (R1CS Native) (IsZero.interface (bit Native)) := IsZero.impl R1CS.arith

def assertEqExpr : Impl (ExprBackend Native) AssertEq.interface := AssertEq.impl ExprBackend.arith
def assertEqR1CS : Impl (R1CS Native) AssertEq.interface := AssertEq.impl R1CS.arith

def isEqualExpr : Impl (ExprBackend Native) (IsEqual.interface (bit Native)) := IsEqual.impl ExprBackend.arith isZeroExpr
def isEqualR1CS : Impl (R1CS Native) (IsEqual.interface (bit Native)) := IsEqual.impl R1CS.arith isZeroR1CS

/-! ## Inverses -/

def inverseExpr : Impl (ExprBackend Native) Inverse.interface := Inverse.impl ExprBackend.arith
def inverseR1CS : Impl (R1CS Native) Inverse.interface := Inverse.impl R1CS.arith

def assertNonZeroExpr : Impl (ExprBackend Native) AssertNonZero.interface := AssertNonZero.impl inverseExpr
def assertNonZeroR1CS : Impl (R1CS Native) AssertNonZero.interface := AssertNonZero.impl inverseR1CS

def divExpr : Impl (ExprBackend Native) Div.interface := Div.impl ExprBackend.arith inverseExpr
def divR1CS : Impl (R1CS Native) Div.interface := Div.impl R1CS.arith inverseR1CS

/-! ## Selection -/

section
open Gates

def muxExpr : Impl (ExprBackend Native) (MUX.interface (bit Native)) := MUX.impl ExprBackend.arith
def muxR1CS : Impl (R1CS Native) (MUX.interface (bit Native)) := MUX.impl R1CS.arith

def chExpr : Impl (ExprBackend Native) (CH.interface (bit Native)) := CH.impl andExpr orExpr notExpr
def chR1CS : Impl (R1CS Native) (CH.interface (bit Native)) := CH.impl andR1CS orR1CS notR1CS

def majExpr : Impl (ExprBackend Native) (MAJ.interface (bit Native)) := MAJ.impl andExpr orExpr
def majR1CS : Impl (R1CS Native) (MAJ.interface (bit Native)) := MAJ.impl andR1CS orR1CS

end

/-! ## Bits to number -/

def bits2numExpr (n : ℕ) : Impl (ExprBackend Native) (Bits2Num.interface (bit Native) n) := Bits2Num.impl ExprBackend.arith n
def bits2numR1CS (n : ℕ) : Impl (R1CS Native) (Bits2Num.interface (bit Native) n) := Bits2Num.impl R1CS.arith n

end Clean2
