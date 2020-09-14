import sbt.Keys.libraryDependencies
import sbtcrossproject.CrossPlugin.autoImport.{CrossType, crossProject}

lazy val root = project
  .in(file("."))
  .aggregate(scalaamJS, scalaamJVM)

lazy val scalaam = crossProject(JVMPlatform, JSPlatform)
  .withoutSuffixFor(JVMPlatform)
  .crossType(CrossType.Full)
  .in(file("code"))
  .settings(
    /** General settings */
    name := "scalaam",
    version := "2.2",
    scalaVersion := "2.13.3",
    /** Dependencies */
    libraryDependencies += "org.scala-lang.modules" %%% "scala-parser-combinators" % "1.1.2",
    libraryDependencies += "au.com.bytecode"        % "opencsv"                    % "2.4",
    libraryDependencies += "com.typesafe.akka"      %% "akka-actor-typed"          % "2.6.8",
    libraryDependencies += "ch.qos.logback"         % "logback-classic"            % "1.2.3",
    libraryDependencies += "com.typesafe"           % "config"                     % "1.4.0",
    /** Compilation options */
    maxErrors := 5,
    /** Configuration for running the tests */
    logBuffered in Test := false,
    libraryDependencies += "org.scalatest"        %% "scalatest"       % "3.1.1"   % "test",
    libraryDependencies += "org.scalacheck"       %% "scalacheck"      % "1.14.3"  % "test",
    libraryDependencies += "org.scalatestplus"    %% "scalacheck-1-14" % "3.1.0.0" % "test",
    libraryDependencies += "com.vladsch.flexmark" % "flexmark-all"     % "0.35.10" % Test,
    /** Imported options from https://tpolecat.github.io/2017/04/25/scalac-flags.html */
    scalacOptions ++= Seq(
      "-deprecation", // Emit warning and location for usages of deprecated APIs.
      "-encoding",
      "utf-8",                         // Specify character encoding used by source files.
      "-explaintypes",                 // Explain type errors in more detail.
      "-feature",                      // Emit warning and location for usages of features that should be imported explicitly.
      "-language:existentials",        // Existential types (besides wildcard types) can be written and inferred
      "-language:experimental.macros", // Allow macro definition (besides implementation and application)
      "-language:higherKinds",         // Allow higher-kinded types
      "-language:implicitConversions", // Allow definition of implicit functions called views
      "-unchecked",                    // Enable additional warnings where generated code depends on assumptions.
      "-Xcheckinit",                   // Wrap field accessors to throw an exception on uninitialized access.
      //"-Xfatal-warnings",                  // Fail the compilation if there are any warnings.
      //"-Xfuture",                          // Turn on future language features.
      "-Xlint:adapted-args", // Warn if an argument list is modified to match the receiver.
      //"-Xlint:by-name-right-associative",  // By-name parameter of right associative operator.
      "-Xlint:constant",               // Evaluation of a constant arithmetic expression results in an error.
      "-Xlint:delayedinit-select",     // Selecting member of DelayedInit.
      "-Xlint:doc-detached",           // A Scaladoc comment appears to be detached from its element.
      "-Xlint:inaccessible",           // Warn about inaccessible types in method signatures.
      "-Xlint:infer-any",              // Warn when a type argument is inferred to be `Any`.
      "-Xlint:missing-interpolator",   // A string literal appears to be missing an interpolator id.
      "-Xlint:nullary-unit",           // Warn when nullary methods return Unit.
      "-Xlint:option-implicit",        // Option.apply used implicit view.
      "-Xlint:package-object-classes", // Class or object defined in package object.
      "-Xlint:poly-implicit-overload", // Parameterized overloaded implicit methods are not visible as view bounds.
      "-Xlint:private-shadow",         // A private field (or class parameter) shadows a superclass field.
      "-Xlint:stars-align",            // Pattern sequence wildcard must align with sequence component.
      "-Xlint:type-parameter-shadow",  // A local type parameter shadows a type already in scope.
      //"-Xlint:unsound-match",              // Pattern match may not be typesafe.
      //"-Ypartial-unification",             // Enable partial unification in type constructor inference
      "-Ywarn-dead-code",      // Warn when dead code is identified.
      "-Ywarn-extra-implicit", // Warn when more than one implicit parameter section is defined.
      //"-Ywarn-inaccessible",               // Warn about inaccessible types in method signatures.
      //"-Ywarn-infer-any",                  // Warn when a type argument is inferred to be `Any`.
      //"-Ywarn-nullary-override",           // Warn when non-nullary `def f()' overrides nullary `def f'.
      //"-Ywarn-nullary-unit",               // Warn when nullary methods return Unit.
      "-Ywarn-numeric-widen",    // Warn when numerics are widened.
      "-Ywarn-unused:implicits", // Warn if an implicit parameter is unused.
      "-Ywarn-unused:imports",   // Warn if an import selector is not referenced.
      "-Ywarn-unused:locals",    // Warn if a local definition is unused.
      //"-Ywarn-unused:params",              // Warn if a value parameter is unused.
      "-Ywarn-unused:patvars", // Warn if a variable bound in a pattern is unused.
      "-Ywarn-unused:privates" // Warn if a private member is unused.
      // "-Ywarn-value-discard"               // Warn when non-Unit expression results are unused.
    )
  )
  .jvmSettings(
    /** General */
    mainClass in Compile := Some("scalaam.cli.Main"),
    Compile / unmanagedJars += {
      baseDirectory.value / "lib" / "com.microsoft.z3.jar"
    }
  )
  .jsSettings(
    /** General */
    mainClass in Compile := Some("scalaam.web.Main"),
    scalaJSUseMainModuleInitializer := true,
    /** Dependencies */
    libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "0.9.8"
  )

lazy val scalaamJVM = scalaam.jvm
lazy val scalaamJS  = scalaam.js
