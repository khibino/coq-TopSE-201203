object CoqMain {
sealed abstract class List[A]
case class Nil[A]() extends List[A]
case class Cons[A](x1: A, x2: List[A]) extends List[A]
def app[A] : (List[A] => (List[A] => List[A])) = {
(l:List[A]) => (m:List[A]) =>
l match {
case Nil() => m
case Cons(a, l1) => Cons(a, app(l1)(m))
}
}
def rev[A] : (List[A] => List[A]) = {
(l:List[A]) =>
l match {
case Nil() => Nil()
case Cons(x, l$prime) => app[A](rev(l$prime))(Cons(x, Nil()))
}
}
}
