package scalaam

object Main {
  def main(args: Array[String]) {
    import scalaam.language.lambda._
    import scalaam.machine._
    import scalaam.core._
    import scalaam.graph._

    val address = NameAddress
    val timestamp = ZeroCFA[Unit]()
    val lattice = LambdaSetLattice[address.A]()
    val sem = LambdaSemantics[lattice.L, address.A, timestamp.T, Unit](address.Alloc[timestamp.T, Unit])
    val machine = new AAM[LambdaExp, lattice.L, address.A, timestamp.T, Unit](sem)
    val graph = DotGraph.empty[machine.State, machine.Transition]
    val result = machine.run(LambdaParser.parse("((lambda (x) (lambda (y) y)) (lambda (z) z))"), graph, Timeout.Infinity)
    result.asInstanceOf[DotGraph[machine.State, machine.Transition]].toFile("foo.dot")
    println(result)
  }
}
