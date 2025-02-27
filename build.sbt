import Dependencies._

ThisBuild / scalaVersion     := "2.13.15"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "com.example"
ThisBuild / organizationName := "example"

lazy val root = (project in file("."))
  .settings(
    name := "mub_search_scala",
    libraryDependencies ++= Seq(
      "com.monovore" %% "decline" % "1.3.0",
      "org.typelevel" %% "spire" % "0.18.0",
      "org.typelevel" %% "algebra" % "2.12.0",
      "org.typelevel" %% "cats-core" % "2.12.0",
      "org.typelevel" %% "paiges-core" % "0.3.2",
      "org.scalameta" %% "munit" % "1.0.4" % Test,
      "org.scalameta" %% "munit-scalacheck" % "1.0.0" % Test,
      "org.scalacheck" %% "scalacheck" % "1.18.1" % Test,
    ),
    scalacOptions ++= Seq(
      "-opt:l:inline",
      "-opt-inline-from:**"
    ),
    testFrameworks += new TestFramework("munit.Framework"),
    assembly / test := {}
  )

// Uncomment the following for publishing to Sonatype.
// See https://www.scala-sbt.org/1.x/docs/Using-Sonatype.html for more detail.

// ThisBuild / description := "Some descripiton about your project."
// ThisBuild / licenses    := List("Apache 2" -> new URL("http://www.apache.org/licenses/LICENSE-2.0.txt"))
// ThisBuild / homepage    := Some(url("https://github.com/example/project"))
// ThisBuild / scmInfo := Some(
//   ScmInfo(
//     url("https://github.com/your-account/your-project"),
//     "scm:git@github.com:your-account/your-project.git"
//   )
// )
// ThisBuild / developers := List(
//   Developer(
//     id    = "Your identifier",
//     name  = "Your Name",
//     email = "your@email",
//     url   = url("http://your.url")
//   )
// )
// ThisBuild / pomIncludeRepository := { _ => false }
// ThisBuild / publishTo := {
//   val nexus = "https://oss.sonatype.org/"
//   if (isSnapshot.value) Some("snapshots" at nexus + "content/repositories/snapshots")
//   else Some("releases" at nexus + "service/local/staging/deploy/maven2")
// }
// ThisBuild / publishMavenStyle := true
