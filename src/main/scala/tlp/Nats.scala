

/* Type Programming */

sealed trait NN {
  type plus[That <: NN] <: NN
}

sealed trait NN0 extends NN {
  override type plus[That <: NN] = That
}

sealed trait NNN[Prev <: NN] extends NN {
  override type plus[That <: NN] = NNN[Prev#plus[That]]
}

/* For now use a different family of types for the bases */
sealed trait Bit

sealed trait Bit0 extends Bit

sealed trait Bit1 extends Bit


sealed trait LN {
  type plus[That <: LN] <: LN
}

// N - 1 bits in lsb-first
sealed trait LNN[PrevBit0 <: Bit, PrevBit1 <: Bit, PrevBit2 <: Bit] extends LN {
  override type plus[That <: LN] = That // TODO
}

sealed trait LN0 extends LN {
  override type plus[That <: LN] = That
}

//sealed trait LN1 extends LNN[LN0, LN0, LN0]  {
//  override type plus[That <: LN] = That // TODO
//}
//
//sealed trait LN2 extends LNN[LN1, LN0, LN0]  {
//  override type plus[That <: LN] = That // TODO
//}
//
//sealed trait LN3 extends LNN[LN0, LN1, LN0]  {
//  override type plus[That <: LN] = That // TODO
//}

// 0, 0, 0 -> 1, 0, 0
// 1, 0, 0 -> 0, 1, 0
// 0, 1, 0 -> 1, 1, 0
// 1, 1, 0 -> 0, 0, 1 etc

// Increment
// S = Switching


//  type plus[That <: NN] <: NN
//  override type plus[That <: NN] = That
//  override type plus[That <: NN] = NNN[Prev#plus[That]]

sealed trait Nat {
  type inc <: Nat
  type dbl <: Nat
  type half <: Nat
  type add[That <: Nat] <: Nat
  // TODO: Better name
  type coreT[That <: Nat] <: Nat
  type mult[That <: Nat] <: Nat

  type exp[That <: Nat] <: Nat
  type expflip[That <: Nat] <: Nat

  //  type 𝟘 = this.type#dbl#dbl#dbl#dbl
  //  type 𝟙 = this.type#dbl#dbl#dbl#dbl#inc
  type A = this.type#dbl#inc#dbl#dbl#inc#dbl
  type B = this.type#dbl#inc#dbl#dbl#inc#dbl#inc
  type C = this.type#dbl#inc#dbl#inc#dbl#dbl
  type D = this.type#dbl#inc#dbl#inc#dbl#dbl#inc
  type E = this.type#dbl#inc#dbl#inc#dbl#inc#dbl
  type F = this.type#dbl#inc#dbl#inc#dbl#inc#dbl#inc
  type multFF = this.type#dbl#dbl#dbl#dbl#dbl#dbl#dbl#dbl
  type mult2to8to8 = this.type#multFF#multFF#multFF#multFF#multFF#multFF#multFF#multFF
}

sealed trait B0[HigherBits <: Nat] extends Nat {
  override type inc = B1[HigherBits]
  override type dbl = B0[B0[HigherBits]]
  override type half = HigherBits
  override type add[That <: Nat] = That#coreT[That#half#add[HigherBits]]
  override type coreT[That <: Nat] = B0[That]
  override type mult[That <: Nat] = HigherBits#mult[That]#dbl
  override type exp[That <: Nat] = That#expflip[B0[HigherBits]]
  override type expflip[That <: Nat] = HigherBits#expflip[That#mult[That]]
}

sealed trait B1[HigherBits <: Nat] extends Nat {
  override type inc = B0[HigherBits#inc]
  override type dbl = B0[B1[HigherBits]]
  override type half = HigherBits
  override type add[That <: Nat] = That#inc#coreT[That#inc#half#add[HigherBits]]
  override type coreT[That <: Nat] = B1[That]
  override type mult[That <: Nat] = HigherBits#mult[That]#dbl#add[That]
  override type exp[That <: Nat] = That#expflip[B1[HigherBits]]
  // a^b -> b = this.type, a = That
  // b = 2n + 1
  // a^(2n + 1) = (a^2)^n * a
  //  override type expflip[That <: Nat] = That#mult[this.type#mult[this.type]#exp[this.type#half]]
  override type expflip[That <: Nat] = HigherBits#expflip[That#mult[That]]#mult[That]
}

sealed trait MsbZero extends Nat {
  override type inc = MsbOne
  override type dbl = MsbZero
  override type half = MsbZero
  override type add[That <: Nat] = That
  override type coreT[That <: Nat] = B0[That]
  override type mult[That <: Nat] = MsbZero
  override type exp[That <: Nat] = MsbZero
  override type expflip[That <: Nat] = MsbOne
}

sealed trait MsbOne extends Nat {
  override type inc = B0[MsbOne]
  override type dbl = B0[MsbOne]
  override type half = MsbZero
  override type add[That <: Nat] = That#inc
  override type coreT[That <: Nat] = B1[That]
  override type mult[That <: Nat] = That
  override type exp[That <: Nat] = MsbOne
  override type expflip[That <: Nat] = That
}

//Need a special type for the highest bit that switches SpecBit1 => B0, SpecBit1

object Main1 extends App {

  // 1 = O + 1
  implicitly[MsbOne =:= MsbZero#inc]

  // 2 = O + 1 + 1
  implicitly[B0[MsbOne] =:= MsbZero#inc#inc]

  // 3 = O + 1 + 1 + 1
  implicitly[B1[MsbOne] =:= MsbZero#inc#inc#inc]

  // 4 = O + 1 + 1 + 1 +
  implicitly[B0[B0[MsbOne]] =:= MsbZero#inc#inc#inc#inc]

  // etc
  implicitly[B1[B0[MsbOne]] =:= MsbZero#inc#inc#inc#inc#inc]
  implicitly[B0[B1[MsbOne]] =:= MsbZero#inc#inc#inc#inc#inc#inc]
  implicitly[B1[B1[MsbOne]] =:= MsbZero#inc#inc#inc#inc#inc#inc#inc]
  implicitly[B0[B0[B0[MsbOne]]] =:= MsbZero#inc#inc#inc#inc#inc#inc#inc#inc]
  implicitly[B1[B0[B0[MsbOne]]] =:= MsbZero#inc#inc#inc#inc#inc#inc#inc#inc#inc]

  // 0 = 0 * 2
  implicitly[MsbZero =:= MsbZero#dbl]

  // 2 = 1 * 2
  implicitly[B0[MsbOne] =:= MsbOne#dbl]

  // 4 = 2 * 2
  implicitly[B0[B0[MsbOne]] =:= B0[MsbOne]#dbl]

  // 6 = 3 * 2
  implicitly[B0[B1[MsbOne]] =:= B1[MsbOne]#dbl]

  type T0 = MsbZero
  type T1 = T0#inc
  type T2 = T1#inc
  type T3 = T2#inc
  type T4 = T3#inc
  type T5 = T4#inc
  type T6 = T5#inc
  type T7 = T6#inc
  type T8 = T7#inc
  type T9 = T8#inc
  type T10 = T9#inc
  type T11 = T10#inc
  type T12 = T11#inc
  type T13 = T12#inc
  type T14 = T13#inc
  type T15 = T14#inc
  type T16 = T15#inc
  type T17 = T16#inc

  implicitly[T17 =:= MsbZero#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc#inc]

  // 17 = 1 * 2 * 2 * 2 * 1 + 1
  implicitly[T17 =:= MsbOne#dbl#dbl#dbl#dbl#inc]

  type T20 = T10#add[T10]
  type T27 = T20#add[T7]

  //  implicitly[MsbZero#half#add[MsbOne] =:= MsbOne]
  //
  //  implicitly[B0[MsbOne] =:= MsbZero#coreT[MsbOne]]
  //
  //  implicitly[B0[MsbOne] <:< MsbZero#coreT[MsbOne]]
  //
  //  implicitly[MsbZero#coreT[MsbOne] <:< B0[MsbOne]]

  //  implicitly[MsbZero#coreT[MsbOne] =:= B0[MsbOne]]

  //  MsbZero#coreT[MsbZero#half#add[MsbOne]] =:= B0[MsbOne]

  implicitly[MsbZero =:= MsbZero#half]
  implicitly[MsbZero =:= MsbOne#half]
  implicitly[MsbOne =:= B0[MsbOne]#half]
  implicitly[MsbOne =:= B1[MsbOne]#half]

  // 0 + 0, 0 + 1
  implicitly[MsbZero#add[MsbZero] =:= MsbZero]

  implicitly[MsbZero#add[MsbOne] =:= MsbOne]

  // 1 + 0, 1 + 1
  implicitly[MsbOne#add[MsbZero] =:= MsbOne]

  implicitly[MsbOne#add[MsbOne] =:= B0[MsbOne]]

  // 2 + 0, 2 + 1, 2 + 2
  implicitly[B0[MsbOne]#add[MsbZero] =:= B0[MsbOne]]

  implicitly[B0[MsbOne]#add[MsbOne] =:= B1[MsbOne]]

  implicitly[B0[MsbOne]#add[B0[MsbOne]] =:= B0[B0[MsbOne]]]

  implicitly[T2#add[T0] =:= T2]
  implicitly[T2#add[T1] =:= T3]
  implicitly[T2#add[T2] =:= T4]

  implicitly[T0#add[T2] =:= T2]
  implicitly[T1#add[T2] =:= T3]
  implicitly[T2#add[T2] =:= T4]

  implicitly[T3#add[T0] =:= T3]
  implicitly[T3#add[T1] =:= T4]
  implicitly[T3#add[T2] =:= T5]
  implicitly[T3#add[T3] =:= T6]

  implicitly[T2#add[T2] =:= T1#add[T3]]

  implicitly[T2#add[T2] =:= T3#add[T1]]

  implicitly[T3#add[T1] =:= T1#add[T3]]

  implicitly[T3#add[T2] =:= T1#add[T4]]

  implicitly[T3#add[T3] =:= T2#add[T4]]
  implicitly[T4#add[T4] =:= T3#add[T5]]

  implicitly[T5#add[T5] =:= T4#add[T6]]
  implicitly[T5#add[T5] =:= T6#add[T4]]
  //
  implicitly[T5#add[T5] =:= T1#add[T2]#add[T3]#add[T4]]

  //  type T10 = T5#dbl
  type T100 = T10#dbl#dbl#dbl#add[T10]#add[T10]

  // 100 base 10 = 1100100 base 2
  implicitly[T100 =:= B0[B0[B1[B0[B0[B1[MsbOne]]]]]]]

  type T1000 = T100#dbl#dbl#dbl#add[T100]#add[T100]

  type F1 = T1
  type F2 = T1
  type F3 = F1#add[F2]
  type F4 = F2#add[F3]
  type F5 = F3#add[F4]
  type F6 = F4#add[F5]
  type F7 = F5#add[F6]

  implicitly[F7 =:= T10#add[T3]]
  implicitly[F7 =:= MsbZero#D]

  // Quadrillion = 10 to 15 = 1000 to 5
  type QuadrillionT = MsbZero#A#A#A#A#A#A#A#A#A#A#A#A#A#A#A

  //  type K = B0[MsbOne]#add[MsbZero]

  //  implicitly[K =:= B0[MsbOne]]
  //
  //  "-" match {
  //    case x: K =>
  //  }

  //  val t = new K {}

  //  val t = new B0[MsbOne]#add[MsbZero] {}

  // 2 + 0, 2 + 1
  //  implicitly[B0[MsbOne] =:= B0[MsbOne]#add[MsbZero]]
  //  implicitly[B1[MsbOne] =:= B0[MsbOne]#add[MsbOne]]

  implicitly[MsbZero#mult[MsbZero] =:= MsbZero]
  implicitly[MsbZero#mult[MsbOne] =:= MsbZero]
  implicitly[MsbOne#mult[MsbZero] =:= MsbZero]
  implicitly[MsbOne#mult[MsbOne] =:= MsbOne]

  implicitly[T0#mult[T0] =:= T0]
  implicitly[T0#mult[T1] =:= T0]
  implicitly[T0#mult[T2] =:= T0]
  implicitly[T0#mult[T3] =:= T0]
  implicitly[T0#mult[T4] =:= T0]

  implicitly[T1#mult[T0] =:= T0]
  implicitly[T1#mult[T1] =:= T1]
  implicitly[T1#mult[T2] =:= T2]
  implicitly[T1#mult[T3] =:= T3]
  implicitly[T1#mult[T4] =:= T4]

  implicitly[T2#mult[T0] =:= T0]
  implicitly[T2#mult[T1] =:= T2]
  implicitly[T2#mult[T2] =:= T4]
  implicitly[T2#mult[T3] =:= T6]
  implicitly[T2#mult[T4] =:= T8]

  implicitly[T3#mult[T0] =:= T0]
  implicitly[T3#mult[T1] =:= T3]
  implicitly[T3#mult[T2] =:= T6]
  implicitly[T3#mult[T3] =:= T9]
  implicitly[T3#mult[T4] =:= T12]

  implicitly[T4#mult[T0] =:= T0]
  implicitly[T4#mult[T1] =:= T4]
  implicitly[T4#mult[T2] =:= T8]
  implicitly[T4#mult[T3] =:= T12]
  implicitly[T4#mult[T4] =:= T16]

  type T510 = T5#mult[T10]#add[T1]#mult[T10]
  type T510510 = T510#mult[T1000]#add[T510]

  implicitly[T2#mult[T3]#mult[T5]#mult[T7]#mult[T11]#mult[T13]#mult[T17] =:= T510510]

  // Exponentiation

  // exp on most significant bits

  implicitly[MsbZero#exp[MsbZero] =:= MsbZero]
  implicitly[MsbZero#exp[MsbOne] =:= MsbZero]
  implicitly[MsbZero#exp[T2] =:= MsbZero]
  implicitly[MsbZero#exp[T3] =:= MsbZero]

  implicitly[MsbOne#exp[MsbZero] =:= MsbOne]
  implicitly[MsbOne#exp[MsbOne] =:= MsbOne]
  implicitly[MsbOne#exp[T2] =:= MsbOne]
  implicitly[MsbOne#exp[T3] =:= MsbOne]

  // expflip on most significant bits

  // TODO: 0^0
  //  implicitly[MsbZero#expflip[MsbZero] =:= MsbZero]
  implicitly[MsbZero#expflip[MsbOne] =:= MsbOne]
  implicitly[MsbZero#expflip[T2] =:= MsbOne]
  implicitly[MsbZero#expflip[T3] =:= MsbOne]

  implicitly[MsbOne#expflip[MsbZero] =:= MsbZero]
  implicitly[MsbOne#expflip[MsbOne] =:= MsbOne]
  implicitly[MsbOne#expflip[T2] =:= T2]
  implicitly[MsbOne#expflip[T3] =:= T3]

  // expflip

  // 1^0
  implicitly[T0#expflip[T1] =:= T1]
  // 1^1
  implicitly[T1#expflip[T1] =:= T1]
  // 1^2
  implicitly[T2#expflip[T1] =:= T1]
  // 1^3
  implicitly[T3#expflip[T1] =:= T1]

  // 2^0
  implicitly[T0#expflip[T2] =:= T1]
  // 2^1
  implicitly[T1#expflip[T2] =:= T2]
  // 2^2
  implicitly[T2#expflip[T2] =:= T4]
  // 2^3
  implicitly[T3#expflip[T2] =:= T8]

  // 3^0
  implicitly[T0#expflip[T3] =:= T1]
  // 3^1
  implicitly[T1#expflip[T3] =:= T3]
  // 3^2
  implicitly[T2#expflip[T3] =:= T9]
  // 3^3
  implicitly[T3#expflip[T3] =:= T27]

  // exp

  // 1^0
  implicitly[T1#exp[T0] =:= T1]
  // 1^1
  implicitly[T1#exp[T1] =:= T1]
  // 1^2
  implicitly[T1#exp[T2] =:= T1]
  // 1^3
  implicitly[T1#exp[T3] =:= T1]

  // 2^0
  implicitly[T2#exp[T0] =:= T1]
  // 2^1
  implicitly[T2#exp[T1] =:= T2]
  // 2^2
  implicitly[T2#exp[T2] =:= T4]
  // 2^3
  implicitly[T2#exp[T3] =:= T8]

  // 3^0
  implicitly[T3#exp[T0] =:= T1]
  // 3^1
  implicitly[T3#exp[T1] =:= T3]
  // 3^2
  implicitly[T3#exp[T2] =:= T9]
  // 3^3
  implicitly[T3#exp[T3] =:= T27]

  //  implicitly[T2#exp[T0] =:= T1]
  //  implicitly[T2#exp[T1] =:= T2]
  //  implicitly[T2#exp[T2] =:= T4]
  //  implicitly[T2#exp[T3] =:= T8]
  //  implicitly[T2#exp[T4] =:= T16]

  implicitly[T10#exp[T2] =:= T100]

  // T2 = 15
  // T3 = 9

  type Quadrillion2 = T10#exp[T15]

  type Test = T10#exp[T15]
  type Test2 = T10#exp[T15]

  implicitly[Test =:= Test2]
  //  implicitly[T10#exp[T2] =:= QuadrillionT] // Long compile time
  //  implicitly[T10#exp[T15] =:= QuadrillionT] // Long compile time
  // TODO exponentiate 0 !
}
