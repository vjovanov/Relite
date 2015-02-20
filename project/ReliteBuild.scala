import sbt._
import Keys._

object ReliteBuild extends Build {

  lazy val relite = Project(id = "relite", base = file("."))

  lazy val generated = Project(id = "generated", base = file("generated"))

}
