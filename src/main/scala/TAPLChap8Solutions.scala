import stainless.lang.*
import stainless.annotation.*

object TAPLChap8Solutions {

  def Unreachable: Nothing = ???

  sealed trait Type

  case object Bool extends Type
  case object Int extends Type

  sealed trait TypeDerivation{

    // The term typed by this derivation
    def term: Term = 
      this match
        case TrueTypeDerivation => True
        case FalseTypeDerivation => False
        case IteTypeDerivation(cond, thenBranch, elseBranch) => Ite(cond.term, thenBranch.term, elseBranch.term)
        case ZeroTypeDerivation => Zero
        case SuccTypeDerivation(td) => Succ(td.term)
        case PredTypeDerivation(td) => Pred(td.term)
        case IsZeroTypeDerivation(td) => IsZero(td.term)
    
    // The type of this derivation
    def typ: Type = 
      this match
        case TrueTypeDerivation => Bool
        case FalseTypeDerivation => Bool
        case IteTypeDerivation(cond, thenBranch, elseBranch) => thenBranch.typ
        case ZeroTypeDerivation => Int
        case SuccTypeDerivation(td) => Int
        case PredTypeDerivation(td) => Int
        case IsZeroTypeDerivation(td) => Bool

    // Whether this derivation is sound
    def isSound: Boolean =
      this match
        case TrueTypeDerivation => true
        case FalseTypeDerivation => true
        case IteTypeDerivation(cond, thenBranch, elseBranch) => 
          cond.isSound && thenBranch.isSound && elseBranch.isSound &&
          cond.typ == Bool && thenBranch.typ == elseBranch.typ
        case ZeroTypeDerivation => true
        case SuccTypeDerivation(td) => td.isSound && td.typ == Int
        case PredTypeDerivation(td) => td.isSound && td.typ == Int
        case IsZeroTypeDerivation(td) => td.isSound && td.typ == Int

    // The size of this derivation
    def size: BigInt = {
      this match
        case IteTypeDerivation(cond, thenBranch, elseBranch) => 1 + cond.size + thenBranch.size + elseBranch.size
        case SuccTypeDerivation(td) => 1 + td.size
        case PredTypeDerivation(td) => 1 + td.size
        case IsZeroTypeDerivation(td) => 1 + td.size
        case _ => BigInt(1)
    }.ensuring(_ > 0)
  }

  case object TrueTypeDerivation extends TypeDerivation
  case object FalseTypeDerivation extends TypeDerivation
  case class IteTypeDerivation(cond: TypeDerivation, thenBranch: TypeDerivation, elseBranch: TypeDerivation) extends TypeDerivation
  case object ZeroTypeDerivation extends TypeDerivation
  case class SuccTypeDerivation(td: TypeDerivation) extends TypeDerivation
  case class PredTypeDerivation(td: TypeDerivation) extends TypeDerivation
  case class IsZeroTypeDerivation(td: TypeDerivation) extends TypeDerivation


  /**
    * Type inference algorithm
    *
    * @param t the term to infer the type of
    * @return A type derivation if the term has a type, None otherwise
    */
  def typeInference(t: Term): Option[TypeDerivation] = {
    t match
      case True => Some(TrueTypeDerivation)
      case False => Some(FalseTypeDerivation)
      case Ite(cond, thenBranch, elseBranch) =>
        (typeInference(cond), typeInference(thenBranch), typeInference(elseBranch)) match
          case (Some(condTd), Some(thenTd), Some(elseTd)) if condTd.typ == Bool && thenTd.typ == elseTd.typ =>
            Some(IteTypeDerivation(condTd, thenTd, elseTd))
          case _ => None()
      case Zero => Some(ZeroTypeDerivation)
      case Succ(n) => 
        typeInference(n) match 
          case Some(body) if body.typ == Int => Some(SuccTypeDerivation(body))
          case _ => None()
      case Pred(n) => 
        typeInference(n) match 
          case Some(body) if body.typ == Int => Some(PredTypeDerivation(body))
          case _ => None()
      case IsZero(n) => 
        typeInference(n) match 
          case Some(body) if body.typ == Int => Some(IsZeroTypeDerivation(body))
          case _ => None()
  }.ensuring(res => res.isDefined ==>( res.get.isSound && res.get.term == t))

  /**
    * Completeness of the type inference algorithm
    * Every sound type derivation is a result of the type inference algorithm
    */
  @opaque
  def typeInferenceCompleteness(td: TypeDerivation): Unit = {
    require(td.isSound)

    td match
      case IteTypeDerivation(cond, thenBranch, elseBranch) =>
        typeInferenceCompleteness(cond)
        typeInferenceCompleteness(thenBranch)
        typeInferenceCompleteness(elseBranch)
      case SuccTypeDerivation(body) => typeInferenceCompleteness(body)
      case PredTypeDerivation(body) => typeInferenceCompleteness(body)
      case IsZeroTypeDerivation(body) => typeInferenceCompleteness(body)
      case _ => ()
  }.ensuring(typeInference(td.term) == Some(td))

  /**
    * Every sound type derivation is unique
    * This ones come for free thanks to your awesome type inference algorithm!
    */
  @opaque
  def uniqueTypeDerivation(td1: TypeDerivation, td2: TypeDerivation): Unit = {
    require(td1.isSound && td2.isSound)
    require(td1.term == td2.term)
    require(td1.typ == td2.typ)

    typeInferenceCompleteness(td1)
    typeInferenceCompleteness(td2)
    
  }.ensuring(td1 == td2)


  sealed trait Term {
    def isNumericalValue: Boolean = 
      this match 
        case Zero => true
        case Succ(n) => n.isNumericalValue
        case _ => false
    

    def isValue: Boolean = 
      this match 
        case True => true
        case False => true
        case _ => isNumericalValue
  }

  case object True extends Term
  case object False extends Term
  case class Ite(cond: Term, thenBranch: Term, elseBranch: Term) extends Term
  case object Zero extends Term
  case class Succ(n: Term) extends Term
  case class Pred(n: Term) extends Term
  case class IsZero(n: Term) extends Term

  sealed trait EvalDerivation{

      // The term before the evaluation step
      def term1: Term = {
        this match
          case PredEvalDerivation(rd) => Pred(rd.term1)
          case SuccEvalDerivation(rd) => Succ(rd.term1)
          case isZeroEvalDerivation(rd) => IsZero(rd.term1)
          case IteTrueEvalDerivation(thenBranch, elseBranch) => Ite(True, thenBranch, elseBranch)
          case IteFalseEvalDerivation(thenBranch, elseBranch) => Ite(False, thenBranch, elseBranch)
          case IteCondEvalDerivation(thenBranch, elseBranch, rd) => Ite(rd.term1, thenBranch, elseBranch)
          case PredZeroEvalDerivation => Pred(Zero)
          case PredSuccEvalDerivation(v) => Pred(Succ(v))
          case IsZeroZeroEvalDerivation => IsZero(Zero)
          case IsZeroSuccEvalDerivation(v) => IsZero(Succ(v))
      }.ensuring(!_.isValue)

      // The term after the evaluation step
      def term2: Term =
        this match
          case PredEvalDerivation(rd) => Pred(rd.term2)
          case SuccEvalDerivation(rd) => Succ(rd.term2)
          case isZeroEvalDerivation(rd) => IsZero(rd.term2)
          case IteTrueEvalDerivation(thenBranch, elseBranch) => thenBranch
          case IteFalseEvalDerivation(thenBranch, elseBranch) => elseBranch
          case IteCondEvalDerivation(thenBranch, elseBranch, rd) => Ite(rd.term2, thenBranch, elseBranch)
          case PredZeroEvalDerivation => Zero
          case PredSuccEvalDerivation(v) => v
          case IsZeroZeroEvalDerivation => True
          case IsZeroSuccEvalDerivation(v) => False

      // Whether the evaluation step is sound
      def isSound: Boolean = 
        this match
          case PredEvalDerivation(rd) => rd.isSound
          case SuccEvalDerivation(rd) => rd.isSound
          case isZeroEvalDerivation(rd) => rd.isSound
          case IteCondEvalDerivation(thenBranch, elseBranch, rd) => rd.isSound
          case PredSuccEvalDerivation(v) => v.isNumericalValue
          case IsZeroSuccEvalDerivation(v) => v.isNumericalValue
          case _ => true

      // The size of this derivation
      def size: BigInt = {
        this match
          case PredEvalDerivation(rd) => 1 + rd.size
          case SuccEvalDerivation(rd) => 1 + rd.size
          case isZeroEvalDerivation(rd) => 1 + rd.size
          case IteCondEvalDerivation(thenBranch, elseBranch, rd) => 1 + rd.size
          case _ => BigInt(1)
      }.ensuring(_ > 0)
          
    }

  case class PredEvalDerivation(rd: EvalDerivation) extends EvalDerivation
  case class SuccEvalDerivation(rd: EvalDerivation) extends EvalDerivation
  case class isZeroEvalDerivation(rd: EvalDerivation) extends EvalDerivation
  case class IteTrueEvalDerivation(thenBranch: Term, elseBranch: Term) extends EvalDerivation
  case class IteFalseEvalDerivation(thenBranch: Term, elseBranch: Term) extends EvalDerivation
  case class IteCondEvalDerivation(thenBranch: Term, elseBranch: Term, rd: EvalDerivation) extends EvalDerivation
  case object PredZeroEvalDerivation extends EvalDerivation
  case class PredSuccEvalDerivation(v: Term) extends EvalDerivation
  case object IsZeroZeroEvalDerivation extends EvalDerivation
  case class IsZeroSuccEvalDerivation(v: Term) extends EvalDerivation

  /**
    * There is a unique way to derive a sound evaluation step
    */
  @opaque 
  def uniqueEvalDerivation(ed1: EvalDerivation, ed2: EvalDerivation): Unit = {
    decreases(ed1.size + ed2.size)
    require(ed1.isSound && ed2.isSound)
    require(ed1.term1 == ed2.term1)

    (ed1, ed2) match
      case (IteCondEvalDerivation(_, _, rd1), IteCondEvalDerivation(_, _, rd2)) =>
        uniqueEvalDerivation(rd1, rd2)
      case (SuccEvalDerivation(rd1), SuccEvalDerivation(rd2)) =>
        uniqueEvalDerivation(rd1, rd2)
      case (PredEvalDerivation(rd1), PredEvalDerivation(rd2)) =>
        uniqueEvalDerivation(rd1, rd2)
      case (isZeroEvalDerivation(rd1), isZeroEvalDerivation(rd2)) =>
        uniqueEvalDerivation(rd1, rd2)
      case _ => ()
  }.ensuring(ed1 == ed2)

  /**
    * Progress 
    * 
    * If a term is well-typed, then either it is a value or there is a step of evaluation that can be performed
    * 
    * @param td the proof that the term is well-typed
    * @return A proof that an evaluation step can be performed, or None if the term is a value
    */
  @opaque
  def progress(td: TypeDerivation): Option[EvalDerivation] = {
    require(td.isSound)
    td match
      case IteTypeDerivation(cond, thenBranch, elseBranch) =>
        cond.term match
          case True => Some(IteTrueEvalDerivation(thenBranch.term, elseBranch.term))
          case False => Some(IteFalseEvalDerivation(thenBranch.term, elseBranch.term))
          case _ => Some(IteCondEvalDerivation(thenBranch.term, elseBranch.term, progress(cond).get))
      case SuccTypeDerivation(body) => 
        if td.term.isNumericalValue then None() else Some(SuccEvalDerivation(progress(body).get))
      case PredTypeDerivation(body) => 
        body.term match
          case Zero => Some(PredZeroEvalDerivation)
          case Succ(v) if v.isNumericalValue => Some(PredSuccEvalDerivation(v))
          case _ => Some(PredEvalDerivation(progress(body).get))
      case IsZeroTypeDerivation(body) => 
        body.term match
          case Zero => Some(IsZeroZeroEvalDerivation)
          case Succ(v) if v.isNumericalValue => Some(IsZeroSuccEvalDerivation(v))
          case _ => Some(isZeroEvalDerivation(progress(body).get))
      case _ => None()
  }.ensuring(res => 
    res match
      case Some(ed) => ed.isSound && ed.term1 == td.term
      case None() => td.term.isValue
  )

  /**
    * Preservation
    * 
    * If a term is well-typed and can be evaluated, then the result of the evaluation is also well-typed
    * 
    * @param td the proof that the term is well-typed
    * @param ed the proof that the term can be evaluated
    * @return A proof that the result of the evaluation is well-typed
    */
  @opaque
  def preservation(td: TypeDerivation, ed: EvalDerivation): TypeDerivation = {
    decreases(td.size + ed.size)
    require(td.isSound)
    require(ed.isSound)
    require(td.term == ed.term1)
    
    (td, ed) match
      case (IteTypeDerivation(cond, thenBranch, elseBranch), IteCondEvalDerivation(_, _, rd)) =>
        IteTypeDerivation(preservation(cond, rd), thenBranch, elseBranch)
      case (IteTypeDerivation(cond, thenBranch, elseBranch), IteTrueEvalDerivation(_, _)) => thenBranch
      case (IteTypeDerivation(cond, thenBranch, elseBranch), IteFalseEvalDerivation(_, _)) => elseBranch
      case (SuccTypeDerivation(body), SuccEvalDerivation(rd)) => 
        SuccTypeDerivation(preservation(body, rd))
      case (PredTypeDerivation(body), PredEvalDerivation(rd)) => PredTypeDerivation(preservation(body, rd))
      case (PredTypeDerivation(body), PredZeroEvalDerivation) => ZeroTypeDerivation
      case (PredTypeDerivation(body), PredSuccEvalDerivation(v)) => 
        body match
          case SuccTypeDerivation(inner) => inner
          case _ => Unreachable
      case (IsZeroTypeDerivation(body), isZeroEvalDerivation(rd)) => IsZeroTypeDerivation(preservation(body, rd))
      case (IsZeroTypeDerivation(body), IsZeroZeroEvalDerivation) => TrueTypeDerivation
      case (IsZeroTypeDerivation(body), IsZeroSuccEvalDerivation(v)) => FalseTypeDerivation
      case _ => Unreachable

  }.ensuring(res => 
    res.isSound && 
    res.term == ed.term2 && 
    res.typ == td.typ &&
    res.size < td.size
  )

  sealed trait MultiStepEvaluationDerivation {
    // The term before the sequence of evaluation steps
    def term1: Term = 
      this match
        case ReflexiveEvaluation(t) => t
        case CompositeEvaluation(head, tail) => head.term1

    // The term after the sequence of evaluation steps
    def term2: Term = 
      decreases(this)
      this match
        case ReflexiveEvaluation(t) => t
        case CompositeEvaluation(head, tail) => tail.term2

    // Whether this sequence of evaluation steps is sound
    def isSound: Boolean = 
      decreases(this)
      this match
        case ReflexiveEvaluation(t) => true
        case CompositeEvaluation(head, tail) => 
          head.isSound &&
          tail.isSound &&
          head.term2 == tail.term1
  }

  case class ReflexiveEvaluation(t: Term) extends MultiStepEvaluationDerivation
  case class CompositeEvaluation(head: EvalDerivation, tail: MultiStepEvaluationDerivation) extends MultiStepEvaluationDerivation

  /**
    * Normalization
    * 
    * Any term can be finitely reduced to a value
    * 
    * @param td a proof that the term is well-typed
    * @return A proof that the term can be reduced to a value in a finite number of steps
    */
  @opaque
  def normalization(td: TypeDerivation): MultiStepEvaluationDerivation = {
    require(td.isSound)
    decreases(td.size)
    progress(td) match
      case Some(ed) => CompositeEvaluation(ed, normalization(preservation(td, ed)))
      case None() => ReflexiveEvaluation(td.term)
  }.ensuring( res => res.term1 == td.term && res.term2.isValue && res.isSound)


}