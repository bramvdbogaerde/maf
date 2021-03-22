package maf.web.visualisations.softcontract

import maf.core.Identity
import maf.language.CScheme.CSchemeParser
import maf.language.scheme._
import maf.modular._
import maf.modular.incremental.scheme.SchemeAnalyses._
import maf.modular.scheme._
import maf.modular.scheme.modf._
import maf.modular.worklist._
import maf.util.benchmarks.Timeout
import maf.language.change.CodeVersion._
import maf.web.visualisations.incremental.VisualisableIncrementalModAnalysis

import scala.concurrent.duration._

// Scala.js-related imports
import org.scalajs.dom
import org.scalajs.dom._

import scala.scalajs.js
import maf.modular.scheme.modf.SimpleSchemeModFAnalysis

// Scala.js helpers

object FileInputElement {
  def apply(handler: String => Unit): html.Input = {
    val input = document.createElement("input").asInstanceOf[html.Input]
    input.setAttribute("type", "file")
    input.addEventListener(
      "change",
      (evtUpload: dom.Event) => {
        val file = input.files.item(0)
        val reader = new dom.FileReader()
        reader.onload = (evtLoad: dom.Event) => handler(reader.result.asInstanceOf[String])
        reader.readAsText(file)
      },
      false
    )
    return input
  }
}

/*
object ContractVerificationPage extends Component {

  override def afterRender(): Unit = {
    import scalatags.JsDom.all._

    val results = document.querySelector("#resultcontent")
    val code    = document.querySelector("#code").asInstanceOf[TextArea]
    val safety  = document.querySelector(".safety")

    document
      .querySelector("#submitCode")
      .addEventListener(
        "click",
        (click: MouseEvent) => {
          val sc       = SCExpCompiler.read(code.value)
          val analysis = new ScTestAnalysisWeb(sc)
          def colorCode(code: ScExp): String = {
            val verifiedT = analysis
              .getVerificationResults(analysis.VerifiedTrue)
              .flatMap((t) => List(t._1.pos, t._2.pos))
            val verifiedF = analysis
              .getVerificationResults(analysis.VerifiedFalse)
              .flatMap((t) => List(t._1.pos, t._2.pos))
            val verifiedU = analysis
              .getVerificationResults(analysis.Top)
              .flatMap((t) => List(t._1.pos, t._2.pos))
            val blames = analysis.summary.blames.values.flatten

            val monitors = analysis.verificationResults.keys.map(_.pos).toList

            val printer = new PrettyPrinter() {
              override def print(s: String, idn: Identity = Identity.none) {
                println(verifiedT)
                println(idn.pos)
                if (verifiedT.contains(idn.pos)) {
                  super.print("<span class=\"highlight green\" >" + s + "</span>", idn)
                } else if (verifiedF.contains(idn.pos)) {
                  super.print("<span class=\"highlight red\" >" + s + "</span>", idn)
                } else if (verifiedU.contains(idn.pos)) {
                  super.print("<span class=\"highlight bold\" >" + s + "</span>", idn)
                } else if (monitors.contains(idn.pos)) {
                  super.print("<span class=\"highlight underline\" >" + s + "</span>", idn)
                } else if (blames.exists(_.blamedPosition.pos == idn.pos)) {
                  super.print("<span class=\"highlight blame\" >" + s + "</span>", idn)
                } else {
                  super.print(s, idn)
                }

              }
            }
            code.prettyPrint(printer)
            printer.render
          }

          analysis.analyze()
          safety.innerHTML = ""
          println(analysis.verificationResults)
          if (analysis.summary.blames.isEmpty) {
            results.innerHTML = colorCode(sc)
            safety.appendChild(span(`class` := "safe", "Verified as safe").render)
          } else {
            results.innerHTML = colorCode(sc)
            safety.appendChild(span(`class` := "unsafe", "Could not verify as safe").render)
          }

        },
        useCapture = false
      )
  }

  def render(): dom.Element = {
    import scalatags.JsDom.all._
    div(
      `class` := "main",
      h3("Soft-Contract Verification Demo"),
      div(
        `class` := "editor",
        textarea(id := "code"),
        br(),
        button(
          id := "submitCode",
          "Check"
        )
      ),
      div(
        `class` := "right",
        div(
          `class` := "results",
          pre(id := "resultcontent")
        ),
        div(
          `class` := "safety"
        )
      )
    ).render
  }
}

object Main extends Router {
  def main(args: Array[String]): Unit = routes(
    "/"          -> WebVisualisationPage,
    "/contracts" -> ContractVerificationPage
  )
}
*/
