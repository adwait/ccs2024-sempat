
name := "secant"
version := "0.0.1"

scalaVersion := "2.12.11"
 
scalacOptions += "-feature"
scalacOptions += "-unchecked"
scalacOptions += "-deprecation"

unmanagedJars in Compile += file("lib/org.alloytools.alloy.dist.jar")
unmanagedJars in Compile += file("lib/uclid-fatjar-0.9.5.jar")

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.15" % "test"
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"

libraryDependencies += "org.scala-graph" %% "graph-core" % "1.13.1"
libraryDependencies += "org.scala-graph" %% "graph-dot" % "1.13.0"

libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"
libraryDependencies += "org.json4s" %% "json4s-jackson" % "4.0.3"

resolvers += "jitpack" at "https://jitpack.io"
libraryDependencies += "com.github.dzufferey" %% "scala-smtlib-interface" % "1.0.0"

libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"
// libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2" withSources()

val circeVersion = "0.14.1"
libraryDependencies ++= Seq(
  "io.circe"  %% "circe-core"     % circeVersion,
  "io.circe"  %% "circe-generic"  % circeVersion,
  "io.circe"  %% "circe-parser"   % circeVersion
)

excludeDependencies ++= Seq(
  ExclusionRule("org.slf4j")
)

Compile/mainClass := Some("secant.SemPatMain")

enablePlugins(JavaAppPackaging)