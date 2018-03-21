name := "lambda-cart"

version := "0.1-SNAPSHOT"

organization := "com.github.tomasmikula"

scalaVersion := "2.12.4"

autoCompilerPlugins := true
addCompilerPlugin("org.spire-math" % "kind-projector" % "0.9.6" cross CrossVersion.binary)
addCompilerPlugin("com.github.tomasmikula" % "pascal" % "0.2.1" cross CrossVersion.binary)

scalacOptions ++= Seq(
  "-language:higherKinds",
  "-Xlint",
  "-unchecked",
  "-deprecation",
  "-feature",
//  "-Xfatal-warnings",
  "-Xsource:2.13",
  "-Yno-adapted-args",
  "-Ypartial-unification",
  "-Ywarn-numeric-widen",
  "-Ywarn-unused-import",
  "-Ywarn-value-discard",
  "-Ypatmat-exhaust-depth", "40",
  "-Xfuture")

libraryDependencies ++= Seq(
  "org.scalaz" %% "scalaz-core" % "7.3.0-M20",

  "org.scalatest" %% "scalatest" % "3.0.5" % "test"
)

fork := true
