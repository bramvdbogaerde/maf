package maf.web

import maf.core.Position._
import maf.language.scheme._
import maf.modular._
import maf.modular.adaptive._
import maf.modular.adaptive.scheme._
import maf.modular.adaptive.scheme.adaptiveArgumentSensitivity._
import maf.modular.scheme._
import maf.modular.scheme.modf._
import maf.util.benchmarks.Timeout

// Scala.js-related imports
import org.scalajs.dom
import org.scalajs.dom.{document, html}

import scala.scalajs.js
import maf.modular.scheme.modf.SimpleSchemeModFAnalysis

// Scala.js helpers

object FileInputElement {
  def apply(handler: String => Unit): html.Input = {
    val input = document.createElement("input").asInstanceOf[html.Input]
    input.setAttribute("type","file")
    input.addEventListener("change", (evtUpload: dom.Event) => {
      val file = input.files.item(0)
      val reader = new dom.FileReader()
      reader.onload = (evtLoad: dom.Event) => handler(reader.result.asInstanceOf[String])
      reader.readAsText(file)
    }, false)
    return input
  }
}

object Main {
  val input = FileInputElement(loadFile)

  def main(args: Array[String]): Unit = setupUI()

  def setupUI() = {
    val body = document.body
    body.appendChild(input)
  }

  def loadFile(text: String): Unit = {
    val program = SchemeParser.parse(text)
    val analysis = new SimpleSchemeModFAnalysis(program) with SchemeModFNoSensitivity
                                                         with SchemeConstantPropagationDomain
                                                         with DependencyTracking[SchemeExp]
                                                         with FIFOWorklistAlgorithm[SchemeExp] {
      //override def allocCtx(nam: Option[String], clo: lattice.Closure, args: List[Value], call: Position, caller: Component) = super.allocCtx(nam,clo,args,call,caller)
      def key(cmp: Component) = expr(cmp).idn
      override def step(t: Timeout.T) = {
        val cmp = workList.head
        println(cmp)
        super.step(t)
      }
      override def intraAnalysis(cmp: SchemeModFComponent): IntraAnalysis with BigStepModFIntra = 
        new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra 
    }
    val visualisation = new WebVisualisation(analysis)
    // parameters for the visualisation
    val body = document.body
    val width = js.Dynamic.global.document.documentElement.clientWidth.asInstanceOf[Int]
    val height = js.Dynamic.global.document.documentElement.clientHeight.asInstanceOf[Int]
    visualisation.init(body, width, height)
  }
}
