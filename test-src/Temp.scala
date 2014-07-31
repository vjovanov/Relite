package relite

import r._
import r.data._
import r.data.internal._
import r.builtins.{CallFactory,Primitives}
import r.nodes._
import r.nodes.truffle.{BaseR, RNode}
import com.oracle.truffle.api.frame._;

import org.antlr.runtime._

import java.io._

import scala.collection.JavaConversions._

object Temp{

  def main(args: Array[String]): Unit = {

    DeliteBridge.install()

    def test(prog: String): Unit = {
      val res = RContext.eval(RContext.parseFile(
          new ANTLRInputStream(new ByteArrayInputStream(prog.getBytes))))

      println(res.pretty)
    }

    test("""

  Delite({

    body_x<-c(1,2,3)
    body_y<-c(4,5,6)

    body_mass<-c(10,10,10)
    solar_mass<-25

    offset_momentum <- function() {
      body_x[[1]] <<-  -sum(body_x * body_mass) / solar_mass
    }

    offset_momentum()
    pprint(body_x)  #here fails, staging error - problem with updated vector

    a<-body_x*body_x
    pprint(a)

  })
  
""")
