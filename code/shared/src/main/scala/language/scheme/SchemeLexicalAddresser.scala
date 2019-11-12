package scalaam.language.scheme

import scalaam.core.Identifier

/** Lexical references can either be: */
trait LexicalRef
/** A reference to a primitive in the global environment */
case class PrimRef(nam: String)                     extends LexicalRef {
  override def toString = s"<prim ${nam}>"
}
/** A reference to a local variable */
case class LocalRef(id: Identifier)                 extends LexicalRef {
  override def toString = s"<local ${id.name}>"
}
/** A reference to a non-local variable (in the lexical scope) */
case class NonLocalRef(id: Identifier, depth: Int)  extends LexicalRef {
  override def toString = s"<non-local@${depth} ${id.name}>"
}
/** A reference to a global variable (=> at the top of the lexical scope) */
case class GlobalRef(id: Identifier)                extends LexicalRef {
  override def toString = s"<global ${id.name}>"
}

object SchemeLexicalAddresser {

  type Defs = List[Identifier]

  /** Extract the identifier names of all definitions in a given body
    * Follows R5RS specification on where such definitions can appear */
  def defs(exp: SchemeExp): Defs = defs(List(exp))
  def defs(bdy: List[SchemeExp]): Defs = defs(bdy, Nil)
  def defs(bdy: List[SchemeExp], acc: Defs): Defs = bdy match {
    case SchemeDefineVariable(id,_,_) :: rest =>
      defs(rest, id :: acc)
    case SchemeDefineFunction(id,_,_,_) :: rest =>
      defs(rest, id :: acc)
    case SchemeBegin(exps,_) :: rest =>
      defs(rest, defs(exps, acc))
    case _ :: rest =>
      defs(rest, acc)
    case _ => acc
  }

  /** A frame is a mapping from variable names to the lexical definition site */
  type Frame = Map[String,Identifier]
  /** A scope consists out of multiple frames */
  case class Scope(local: Frame,
                   lexical: List[Frame],
                   global: Set[String])

  /** Given a variable reference, compute the corresponding lexical address in the given scope */
  def resolve(id: Identifier, scope: Scope): LexicalRef =
    scope.local.get(id.name) match {
      case Some(identifier) => LocalRef(identifier)
      case None => resolveLexical(id.name,scope.lexical,1) match {
        case Some((identifier,depth)) if depth == scope.lexical.length =>
          GlobalRef(identifier)
        case Some((identifier,depth)) =>
          NonLocalRef(identifier,depth)
        case None if scope.global.contains(id.name) =>
          PrimRef(id.name)
        case None => throw new Exception(s"Undefined variable reference: $id")
      }
    }
  def resolveLexical(nam: String, frames: List[Frame], depth: Int): Option[(Identifier,Int)] =
    if (frames.isEmpty) { None } else frames.head.get(nam) match {
      case Some(identifier) => Some((identifier,depth))
      case None             => resolveLexical(nam, frames.tail, depth + 1)
    }

  val emptyFrame = Map[String,Identifier]()

  def newFrame(scope: Scope): Scope =
    scope.copy(local    = emptyFrame,
               lexical  = scope.local :: scope.lexical)
  def extend(scope: Scope, id: Identifier): Scope =
    scope.copy(local = scope.local + (id.name -> id))
  def extend(scope: Scope, ids: Iterable[Identifier]): Scope =
    ids.foldLeft(scope)(extend)

  def translateProgram(prg: SchemeExp, global: Set[String]): SchemeExp =
    translate(prg, extend(Scope(emptyFrame,Nil,global), defs(prg)))

  def translate(exp: SchemeExp, scope: Scope): SchemeExp = exp match {
    case vexp: SchemeValue => vexp
    case quoted: SchemeQuoted => quoted
    case SchemeLambda(prs,bdy,pos) =>
      val extScp = extend(newFrame(scope),prs)
      val bdyLex = translateBody(bdy,extScp)
      SchemeLambda(prs,bdyLex,pos)
    case SchemeVar(id) =>
      SchemeVarLex(id, resolve(id, scope))
    case SchemeBegin(eps,pos) =>
      SchemeBegin(translate(eps, scope), pos)
    case SchemeDefineVariable(id,vexp,pos) =>
      val vexpLex = translate(vexp, scope)
      SchemeDefineVariable(id,vexpLex,pos)
    case SchemeDefineFunction(id,prs,bdy,pos) =>
      val extScp = extend(newFrame(scope),prs)
      val bdyLex = translateBody(bdy, extScp)
      SchemeDefineFunction(id,prs,bdyLex,pos)
    case SchemeSet(id, vexp, pos) =>
      val vexpLex = translate(vexp, scope)
      val varAddr = resolve(id, scope)
      SchemeSetLex(id, varAddr, vexpLex, pos)
    case SchemeIf(prd,csq,alt,pos) =>
      SchemeIf(translate(prd,scope),translate(csq,scope),translate(alt,scope),pos)
    case SchemeFuncall(fun,args,pos) =>
      SchemeFuncall(translate(fun,scope),translate(args,scope),pos)
    case SchemeAnd(exps,pos) =>
      SchemeAnd(translate(exps,scope),pos)
    case SchemeOr(exps,pos) =>
      SchemeOr(translate(exps,scope),pos)
    case SchemeLet(bindings,body,pos) =>
      val (vrs,eps) = bindings.unzip
      val bdsLex = vrs.zip(eps.map(translate(_,scope)))
      val bdyLex = translateBody(body, extend(scope, vrs))
      SchemeLet(bdsLex,bdyLex,pos)
    case SchemeLetStar(bindings,body,pos) =>
      var curScp = scope
      val bdsLex = bindings.map { case (id,vexp) =>
        val bnd = (id, translate(vexp, curScp))
        curScp = extend(curScp, id)
        bnd
      }
      val bdyLex = translateBody(body, curScp)
      SchemeLetStar(bdsLex,bdyLex,pos)
    case SchemeLetrec(bindings,body,pos) =>
      val (vrs,eps) = bindings.unzip
      val extScp = extend(scope, vrs)
      val bdsLex = vrs.zip(eps.map(translate(_,extScp)))
      val bdyLex = translateBody(body, extScp)
      SchemeLetrec(bdsLex,bdyLex,pos)
    case SchemeNamedLet(name,bindings,body,pos) =>
      val (prs,eps) = bindings.unzip
      val bdsLex = prs.zip(eps.map(translate(_,scope)))
      val extScp = extend(newFrame(extend(scope, name)), prs)
      val bdyLex = translateBody(body,extScp)
      SchemeNamedLet(name,bdsLex,bdyLex,pos)
    case _ => throw new Exception(s"Unsupported Scheme expression: $exp")
  }

  def translate(bdy: List[SchemeExp], scope: Scope): List[SchemeExp] =
    bdy.map { exp => translate(exp,scope) }

  def translateBody(body: List[SchemeExp], scope: Scope): List[SchemeExp] =
    translate(body, extend(scope, defs(body)))
}