val scala3Version = "3.3.3"  // LTS version compatible with Stainless

lazy val root = project
  .in(file("."))
  .settings(
    name := "union-find",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies += "org.scalameta" %% "munit" % "1.0.0" % Test
  )
