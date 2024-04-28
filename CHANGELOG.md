# Revision history for language-Modula2

## 0.1.4.1 -- 2024-04-27

* Fixed deprecation warnings
* Bumped the upper bound of `filepath`

## 0.1.4 -- 2023-09-26

* Using `OverloadedRecordDot` (GHC >= 9.2) instead of field accessors unsupported by GHC 9.6
* Bumped the upper bounds of `rank2classes`, `transformers`, and `template-haskell`

## 0.1.3 -- 2022-10-23

* Using `autochain` and new imports from grammatical-parsers-0.7

## 0.1.2 -- 2022-10-09

* Compiling with GHC 9
* Incremented dependency bounds and adjusted code
* Shortened the Atts type instances
* Removed the Auto instances of At and Full.Functor, now universal
* Reusing the Language.Oberon.ConstantFolder attribute rules
* Relaxed the ConstantFolder constraints

## 0.1 -- 2020-11-01

* First version. Released on an unsuspecting world.
