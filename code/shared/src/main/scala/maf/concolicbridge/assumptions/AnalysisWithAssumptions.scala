package maf.concolicbridge.assumptions

import maf.modular.contracts.semantics.ScBigStepSemanticsScheme
import maf.concolicbridge.ScModSemanticsCollaborativeTesting
import maf.language.contracts.ScIdentifier
import maf.language.contracts.ScExp
import maf.core.Identity
import maf.language.contracts.ScLattice.AssumedValue
import maf.language.contracts.ScNil
import maf.modular.contracts.semantics.Counter
import maf.concolicbridge.IdentityGenerator
import maf.language.contracts.ScAssumed
import maf.language.contracts.ScLattice.GuardUnverified
import maf.language.contracts.ScLattice.GuardViolated
import maf.language.contracts.ScLattice.GuardVerified
import maf.concolicbridge.assumptions.Tracker.TrackerCounter

trait AnalysisWithAssumptions extends ScBigStepSemanticsScheme with ScModSemanticsCollaborativeTesting { outer =>
  override def intraAnalysis(component: Component): AnalysisWithAssumptionsIntra

  implicit val symCounter: Counter = new Tracker.TrackerCounter(_tracker)

  override def tracker_=(tracker: Tracker): Unit = {
    super.tracker_=(tracker)
    symCounter.asInstanceOf[TrackerCounter].tracker = tracker
  }

  trait AnalysisWithAssumptionsIntra extends ScIntraAnalysisInstrumented with IntraScBigStepSemantics {

    trait Assumption {

      /** The name of the assumption (e.g., pure, value, ...) */
      def name: String

      def run(
          arg: List[ScExp],
          idn: Identity
        ): ScEvalM[PostValue]

      def isViolated(
          name: String,
          _exp: ScExp,
          _args: List[ScExp]
        ): Boolean =
        outer.isViolated(name)

      def isEnabled: Boolean =
        enabledAssumptions(name)

    }

    object Assumption {
      def enabled(name: String): Boolean =
        availableAssumptions(name).isEnabled

      def checkTag(value: PostValue, tag: String): ScEvalM[Boolean] = {
        val assumedValues: List[ScEvalM[Boolean]] = lattice
          .getAssumedValues(value.pure)
          .map(ass =>
            read(ass.simpleContract)
              .map(value => value.pure == lattice.schemeLattice.symbol(tag))
          )
          .toList

        sequence(assumedValues)
          .map(v => v.foldLeft(true)((a, b) => a && b))
          .map(v => v && assumedValues.size >= 1)
      }

      def hasTag(value: PostValue, tag: String): Set[ScEvalM[PostValue]] = {
        lattice
          .getAssumedValues(value.pure)
          .map(ass => {
            read(ass.simpleContract)
              .flatMap(value => {
                if (value.pure == lattice.schemeLattice.symbol(tag)) {
                  read(ass.value)
                } else {
                  void
                }
              })
          })
      }
    }

    /**
     * A simple assumption that simply evaluates the given expression, and
     * tags it with the name of the assumption. Does not expect any arguments.
     */
    case class TaggedAssumption(tag: String) extends Assumption {
      def name: String = tag
      def applyTo(e: ScExp)(gen: IdentityGenerator): ScExp =
        ScAssumed(
          simpleContract = ScIdentifier(tag, gen.nextIdentity),
          arguments = List(e),
          idn = gen.nextIdentity
        )

      def run(
          args: List[ScExp],
          idn: Identity
        ): ScEvalM[PostValue] = {
        assert(args.size == 1)
        val exp = args(0)
        val exprAddr = allocator.alloc(exp.idn)
        val symbolAddr = allocator.alloc(idn)
        for {
          value <- eval(exp)
          _ <- write(exprAddr, value)
          _ <- write(symbolAddr, (lattice.schemeLattice.symbol(tag), ScNil()))
        } yield (lattice.assumedValue(AssumedValue(symbolAddr, exprAddr)), ScNil())
      }
    }

    /**
     *  An assumption that transforms code and might generate assumptions
     *  from another type
     */
    class TransformationAssumption(val name: String) extends Assumption {
      def run(
          arg: List[ScExp],
          idn: Identity
        ): ScEvalM[PS] = ??? // shouldn't be possible

      /**
       * We never actually want to run the assumption
       *  because it is supposed to generate assumptions from other
       *  types
       */
      override def isViolated(
          name: String,
          _exp: ScExp,
          _args: List[ScExp]
        ): Boolean = true
    }

    private var availableAssumptions: Map[String, Assumption] = Map()
    protected def registerAssumption(name: String, ass: Assumption): Unit = {
      availableAssumptions += (name -> ass)
    }

    protected def runAssumption(
        assumptionName: String,
        arguments: List[ScExp],
        idn: Identity
      ): ScEvalM[PostValue] = {
      availableAssumptions(assumptionName).run(arguments, idn)
    }

    override def evalAssumed(
        simpleContract: ScIdentifier,
        arguments: List[ScExp],
        idn: Identity
      ): ScEvalM[PostValue] = {
      val assumption = availableAssumptions(simpleContract.name)
      if (!assumption.isEnabled) {
        // shouldn't happen because it shouldn't be generated in the first place
        throw new Exception("Assumption is being used without it being enabled")
      } else {
        runAssumption(simpleContract.name, arguments, idn)
      }
    }

    /**
     * Evaluate an if/guard expression.
     *  In the abstract semantics this will first look up the
     *  guard and check whether it has been verified or not, if it
     *  is yet to be verified or is violated, it returns the default expression.
     */
    protected def evalIfGuard(
        guardName: ScIdentifier,
        consequent: ScExp,
        alternatives: List[ScExp],
        idn: Identity
      ): ScEvalM[PostValue] = for {
      addr <- lookup(guardName.name)
      value <- read(addr)
      guard <- pure(lattice.getAssumptionGuard(value.pure))
      value <- guard.status match {
        case GuardVerified                   => eval(consequent)
        case GuardUnverified | GuardViolated => eval(alternatives.last)
      }
    } yield value
  }
}
