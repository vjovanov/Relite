/*
 * Copyright (c) 2013 Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/agpl.html.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package relite

import ppl.delite.framework.DeliteApplication
import ppl.delite.framework.Config
import ppl.delite.framework.codegen.delite.{ DeliteCodeGenPkg, TargetDelite }
import ppl.delite.framework.codegen.{ Target }
import ppl.delite.framework.codegen.scala.{ TargetScala }
import ppl.delite.framework.codegen.cuda.{ TargetCuda }
import scala.virtualization.lms.internal.{ GenericFatCodegen }
import scala.virtualization.lms.common.{ SynchronizedArrayBufferOps, SynchronizedArrayBufferOpsExp }
import scala.collection.mutable
import scala.collection.mutable.{ ArrayBuffer, SynchronizedBuffer }
import ppl.tests.scalatest._

import java.io.{ Console => _, _ }
import java.io.{ File, FileSystem }
import optiml.compiler.OptiMLApplicationCompiler
import optiml.compiler.ops._
import optiml.shared.ops._

class MainDeliteRunner extends DeliteTestRunner with OptiMLApplicationCompiler {

  var program: Rep[Int] => Rep[Any] = { x => x } // crashes if we refer to myprog directly!! GRRR ...

  override def main(): Unit = {
    program(0)
  }
}

// *** from delite test runner. call compileAndTest to run an app

object DeliteRunner {

  val MAGICDELIMETER = "!~x02$758209"

  val propFile = new File("delite.properties")
  if (!propFile.exists) throw new TestFailedException("could not find delite.properties", 3)
  val props = new java.util.Properties()
  props.load(new FileReader(propFile))

  // test parameters
  var verbose = props.getProperty("tests.verbose", "false").toBoolean
  var verboseDefs = props.getProperty("tests.verboseDefs", "false").toBoolean
  var threads = props.getProperty("tests.threads", "1")
  val debug = props.getProperty("delite.debug", "false")
  var cacheSyms = false /* NNOOOOOOOOOO!!!!!!!!!!!*/ //props.getProperty("tests.cacheSyms", "true").toBoolean
  var javaHome = new File(props.getProperty("java.home", ""))
  var scalaHome = new File(props.getProperty("scala.vanilla.home", ""))
  var runtimeClasses = new File(props.getProperty("runtime.classes", ""))
  var runtimeExternalProc = false // scalaHome and runtimeClasses only required if runtimeExternalProc is true. should this be configurable? or should we just remove execTestExternal?

  var javaBin = new File(javaHome, "bin/java")
  var scalaCompiler = new File(scalaHome, "lib/scala-compiler.jar")
  var scalaLibrary = new File(scalaHome, "lib/scala-library.jar")

  def validateParameters() {
    if (!javaHome.exists) throw new TestFailedException("java.home must be a valid path in delite.properties", 3)
    else if (!javaBin.exists) throw new TestFailedException("Could not find valid java installation in " + javaHome, 3)
    else if (runtimeExternalProc && !scalaHome.exists) throw new TestFailedException("scala.vanilla.home must be a valid path in delite.proeprties", 3)
    else if (runtimeExternalProc && (!scalaCompiler.exists || !scalaLibrary.exists)) throw new TestFailedException("Could not find valid scala installation in " + scalaHome, 3)
    else if (runtimeExternalProc && !runtimeClasses.exists) throw new TestFailedException("runtime.classes must be a valid path in delite.properties", 3)
  }

  def compileAndTest(app: DeliteTestRunner) {
    compileAndTest2(app, app.getClass.getName.replaceAll("\\$", ""))
  }

  def compileAndTest2(app: DeliteTestRunner, uniqueTestName: String) {
    println("=================================================================================================")
    println("TEST: " + app.toString)
    println("=================================================================================================")

    validateParameters()
    val args = Array(uniqueTestName + "-test.deg")
    app.resultBuffer = new ArrayBuffer[Boolean] with SynchronizedBuffer[Boolean]
    stageTest(app, args(0), uniqueTestName)
    val outStr = execTest(app, args, uniqueTestName) // if (runtimeExternalProc..)?
    checkTest(app, outStr)
  }

  def stageTest(app: DeliteTestRunner, degName: String, uniqueTestName: String) = {
    println("STAGING...")
    val save = Config.degFilename
    val buildDir = Config.buildDir
    val saveCacheSyms = Config.cacheSyms
    val generatedDir = (new File("generated")).getAbsolutePath + /*protobuf wants absolute path*/
      java.io.File.separator + uniqueTestName
    try {
      Config.degFilename = degName
      Config.buildDir = generatedDir
      Config.cacheSyms = cacheSyms
      Config.debug = debug.toBoolean
      //Config.generateCUDA = true
      val screenOrVoid = if (verbose) System.out else new PrintStream(new ByteArrayOutputStream())
      Console.withOut(screenOrVoid) {
        app.main(Array())
        if (verboseDefs) app.globalDefs.foreach { d => //TR print all defs
          println(d)
          //val s = d match { case app.TP(sym,_) => sym; case app.TTP(syms,_,_) => syms(0); case _ => sys.error("unknown Stm type: " + d) }
          //val info = s.sourceInfo.drop(3).takeWhile(_.getMethodName != "main")
          //println(info.map(s => s.getFileName + ":" + s.getLineNumber).distinct.mkString(","))
        }
        //assert(!app.hadErrors) //TR should enable this check at some time ...
      }
    } finally {
      // concurrent access check
      assert(Config.buildDir == generatedDir)
      Config.degFilename = save
      Config.buildDir = buildDir
      Config.cacheSyms = saveCacheSyms
    }
  }

  def execTest(app: DeliteTestRunner, args: Array[String], uniqueTestName: String) = {
    println("EXECUTING...")
    val name = "test.tmp"
    System.setProperty("delite.runs", 1.toString)
    System.setProperty("delite.threads", threads.toString)
    System.setProperty("delite.home", Config.homeDir)
    //System.setProperty("delite.cuda", 1.toString)
    System.setProperty("delite.code.cache.home", System.getProperty("user.dir") + java.io.File.separator + "generatedCache" + java.io.File.separator + uniqueTestName)
    //Console.withOut(new PrintStream(new FileOutputStream(name))) {
    println("test output for: " + app.toString)
    // NOTE: DeliteCodegen (which computes app.staticDataMap) does not know about VConstantPool!!!
    val staticDataMap = app match {
      //case app: Base_LMS => app.VConstantPool.map(kv=>kv._1.toString->kv._2).toMap
      case app => app.staticDataMap
    }
    ppl.delite.runtime.Delite.embeddedMain(args, staticDataMap) // was: app.staticDataMap
    //}
    /*val buf = new Array[Byte](new File(name).length().toInt)
    val fis = new FileInputStream(name)
    fis.read(buf)
    fis.close()
    val r = new String(buf)
    if (verbose) System.out.println(r)
    r*/ ""
  }

  def checkTest(app: DeliteTestRunner, outStr: String) {
    println("CHECKING...")
    /*val resultStr = outStr substring (outStr.indexOf(MAGICDELIMETER) + MAGICDELIMETER.length, outStr.lastIndexOf(MAGICDELIMETER))
    val results = resultStr split ","
    for (i <- 0 until results.length) {
      if (verbose) print("  condition " + i + ": ")
      val passed = results(i).toLowerCase() == "true"
      if (verbose)
        if (passed) println("PASSED") else println("FAILED")
      assert(passed)
    }*/
  }
}

class TestFailedException(s: String, i: Int) extends Exception(s)

trait DeliteTestRunner extends DeliteApplication with DeliteTestConfig with DeliteTestOpsExp {
  self: optiml.compiler.OptiMLApplicationCompiler =>

  var resultBuffer: ArrayBuffer[Boolean] = _

  def collector: Rep[ArrayBuffer[Boolean]] = staticData(resultBuffer)

  def main(): Unit

  def collect(s: Rep[Boolean]) { delite_test_append(collector, s); println(s) }

  def mkReport(): Rep[Unit] = {
    // println(unit(DeliteRunner.MAGICDELIMETER) + (collector mkString unit(",")) + unit(DeliteRunner.MAGICDELIMETER))
  }
}
