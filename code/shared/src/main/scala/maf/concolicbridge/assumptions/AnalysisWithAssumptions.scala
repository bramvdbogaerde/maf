package maf.concolicbridge.assumptions

import maf.modular.contracts.semantics.ScBigStepSemanticsScheme
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScExp
import maf.core.Identity
import maf.language.contracts.ScLattice.AssumedValue
import maf.language.contracts.ScNil

trait AnalysisWithAssumptions extends ScBigStepSemanticsScheme with ScModSemanticsCollaborativeTesting {
  override def intraAnalysis(component: Component): AnalysisWithAssumptionsIntra

  trait AnalysisWithAssumptionsIntra extends ScIntraAnalysisInstrumented with IntraScBigStepSemantics {
    trait Assumption {
      def run(
          exp: ScExp,
          arg: List[ScExp],
          idn: Identity
        ): ScEvalM[PostValue]
    }

    object Assumption {
      def hasTag(value: PostValue, tag: String): Set[ScEvalM[PostValue]] = {
        lattice
          .getAssumedValues(value.pure)
          .map(ass =>
            read(ass.simpleContract)
              .flatMap(value =>
                if (value.pure == lattice.schemeLattice.symbol(tag)) {
                  read(ass.value)
                } else {
                  void
                }
              )
          )
      }
    }

    /**
     * A simple assumption that simply evaluates the given expression, and
     * tags it with the name of the assumption. Does not expect any arguments.
     */
    case class TaggedAssumption(tag: String) extends Assumption {
      def run(
          exp: ScExp,
          args: List[ScExp],
          idn: Identity
        ): ScEvalM[PostValue] = {
        assert(args.size == 0)
        val exprAddr = allocator.alloc(exp.idn)
        val symbolAddr = allocator.alloc(idn)
        for {
          value <- eval(exp)
          _ <- write(exprAddr, value)
          _ <- write(symbolAddr, (lattice.schemeLattice.symbol(tag), ScNil()))
        } yield (lattice.assumedValue(AssumedValue(symbolAddr, exprAddr)), ScNil())
      }
    }

    private var availableAssumptions: Map[String, Assumption] = Map()
    protected def registerAssumption(name: String, ass: Assumption): Unit = {
      availableAssumptions += (name -> ass)
    }

    protected def runAssumption(
        name: String,
        exp: ScExp,
        arguments: List[ScExp],
        idn: Identity
      ): ScEvalM[PostValue] = {
      availableAssumptions(name).run(exp, arguments, idn)
    }

    override def evalAssumed(
        name: ScIdentifier,
        simpleContract: ScIdentifier,
        expr: ScExp,
        arguments: List[ScExp],
        idn: Identity
      ): ScEvalM[PostValue] = {
      if (isViolated(name.name)) {
        // if the assumption was proven to be violated, then
        // we no longer make the assumption
        eval(expr)
      } else {
        runAssumption(name.name, expr, arguments, idn)
      }
    }
  }
}
