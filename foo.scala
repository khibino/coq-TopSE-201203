object CoqMain {
sealed abstract class Nat
case class O() extends Nat
case class S(x1: Nat) extends Nat
def plus : (Nat => (Nat => Nat)) = {
(n:Nat) => (m:Nat) =>
n match {
case O() => m
case S(p) => S(plus(p)(m))
}
}
def mult : (Nat => (Nat => Nat)) = {
(n:Nat) => (m:Nat) =>
n match {
case O() => O()
case S(p) => plus(m)(mult(p)(m))
}
}
def foo : (Nat => (Nat => Nat)) = {
(x:Nat) => (y:Nat) =>
plus(mult(x)(x))(y)
}
}
