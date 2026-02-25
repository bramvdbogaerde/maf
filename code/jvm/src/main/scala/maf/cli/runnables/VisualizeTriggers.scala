package maf.cli.runnables

import maf.core.*
import maf.language.scheme.*
import maf.cli.experiments.worklist.ProgramGenerator
import maf.cli.runnables.AnalyzeWorklistAlgorithms.FIFOanalysis
import maf.cli.runnables.AnalyzeWorklistAlgorithms.LIFOanalysis
import maf.util.MapUtil.invert
import maf.modular.Dependency
import maf.modular.AddrDependency
import maf.util.Writer
import maf.modular.scheme.PrmAddr
import maf.util.graph.SCC
import maf.modular.DependencyTrackingSnapshot

/**
 * Utility to visualize the dependency graph using GraphViz.
 *
 * Each edge represents a dependency and its direction the flow of values. The thickness of an edge represents how many times the dependency has been
 * triggered.object
 */
object VisualizeTriggers:
    import DynamicWorklistAlgorithms.*

    type Exp = SchemeExp

    private val programText: String = ProgramGenerator.upflow2(6)

    private val analyses: Map[String, (Exp) => DynamicWorklistAlgorithms.Analysis] = Map(
      "FIFO" -> FIFOanalysis(theK = 0),
      "LIFO" -> LIFOanalysis(theK = 0),
      "INFLOW" -> deprioritizeLargeInflow(theK = 0),
      "FAIR" -> fairness(theK = 0),
    )

    private def lookupCount(adr: String)(count: Map[Dependency, Int]): Option[Int] =
        count.collectFirst { case (AddrDependency(foundAdr), c) if foundAdr.toString == adr => c }

    /**
     * Returns a DOT graph based on an set of edges and a weight of these edges
     *
     * @param edges
     *   the set of edges
     * @param count
     *   the weight of these edges
     */
    def toDot(edges: Map[String, Set[String]], count: Map[String, Int]): String =
        val edgeString = edges
            .map { case (from, tos) =>
                val theCount = count.get(from).getOrElse(0)
                val color = if theCount == 0 then "black" else if theCount < 0 then "green" else "red"
                tos.map(to => s"\"$from\" -> \"$to\" [penwidth=${Math.abs(theCount) + 1}, color = $color];").mkString("\n")
            }
            .mkString("\n")

        s"digraph { $edgeString }"

    /** Extract the dependency snapshot from the given analysis */
    def snapshot(anl: Analysis): DependencyTrackingSnapshot[anl.Component] =
        DependencyTrackingSnapshot.fromAnalysis(anl)

    /** Computes the edge set and their dependency count for the given snapshot */
    def computeNodes[Cmp](snapshot: DependencyTrackingSnapshot[Cmp]): (Map[String, Set[String]], Map[String, Int]) =
        val reads: Map[String, Set[String]] = snapshot.reads.invert
            .filter { case (PrmAddr(_), _) => false; case _ => true }
            .map { case (k, v) => (k.toString, v.map(_.toString)) }
            .toMap
        val wrts: Map[String, Set[String]] = snapshot.writes.map { case (k, v) => (k.toString, v.map(_.toString)) }.toMap
        val edges = reads ++ wrts
        val weights = edges.map { case (from, _) => (from -> lookupCount(from)(snapshot.count).getOrElse(1)) }.toMap

        (edges, weights)

    def main(arguments: Array[String]): Unit =
        if arguments.size < 2 then println("USAGE: maf ANALYSIS_1 ANALYSIS_2 benchmarks ...")
        else if arguments.size == 2 then println("Usage: maf ANALYSIS_1 ANALYSIS_2 benchmarks ...")
        else
            val args = arguments.toList
            // selected the appropriate analysis
            val selected1 = analyses(args(0))
            val selected2 = analyses(args(1))
            args.drop(2)
                .foreach((suiteName) =>
                    // load the selected benchmarks
                    val suite = suites(suiteName)
                    suite.benchmarks.foreach { case (file, name) =>
                    // println(s"Analyzing $name at $file")
                    // val programText = suite.load(file)
                    // // parse the program
                    // val program = SchemeParser.parseProgram(programText)
                    // // construct the analysis
                    // val anl1 = selected1(program)
                    // val anl2 = selected2(program)
                    // // run the analysis
                    // println(s"Running ${args(0)}")
                    // anl1.analyze()
                    // println(s"Running ${args(1)}")
                    // anl2.analyze()
                    // println("Analysis completed... Constructing graph.")

                    // val (edges1, count1) = computeNodes(snapshot(anl1))
                    // val (_, count2) = computeNodes(snapshot(anl2))
                    // var diffMap: Map[String, Int] = Map()

                    // // The edges should be the same so we ignore the second one
                    // // then we compute the difference between the trigger count in the first and the second
                    // // and only keep the edges that have differences that are different from zero
                    // val edges1p = edges1.flatMap { case (from, tos) =>
                    //     val diff = for
                    //         c1 <- lookupCount(from)(count1)
                    //         c2 <- lookupCount(from)(count2)
                    //     yield c1 - c2
                    //     if diff.isDefined && diff.get != 0 then
                    //         diffMap = diffMap + (from -> diff.get)
                    //         List(from -> tos)
                    //     else if diff.isEmpty then List(from -> tos)
                    //     else List()
                    // }

                    // val contents = toDot(edges1p, diffMap)
                    // val w = Writer.openTimeStamped(s"output/output_${name}.dot")
                    // Writer.write(w, contents)
                    // Writer.close(w)

                    // val (sccs, _) = Tarjan.collapse(edges1.keySet, edges1)
                    // println(s"SCCs in graph: ${sccs.size}")

                    // import sys.process.*
                    // s"sfdp -x -Goverlap=scale -Tpdf \"${Writer.getPath(w)}\" -o /tmp/out.pdf".!
                    // "open /tmp/out.pdf".!
                    }
                )
