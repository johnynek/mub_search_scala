import Dependencies._

ThisBuild / scalaVersion     := "2.13.3"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "com.example"
ThisBuild / organizationName := "example"

lazy val root = (project in file("."))
  .settings(
    name := "mub_search_scala",
    libraryDependencies ++= Seq(
      "com.monovore" %% "decline" % "1.3.0",
      "org.typelevel" %% "spire" % "0.17.0-RC1",
      "org.typelevel" %% "algebra" % "2.0.1",
      "org.typelevel" %% "cats-core" % "2.2.0",
      "org.typelevel" %% "paiges-core" % "0.3.2",
      "com.chuusai" %% "shapeless" % "2.3.3",
      "org.scalameta" %% "munit" % "0.7.12" % Test,
      "org.scalameta" %% "munit-scalacheck" % "0.7.12" % Test,
      "org.scalacheck" %% "scalacheck" % "1.14.3" % Test,
    ),
    testFrameworks += new TestFramework("munit.Framework")
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
