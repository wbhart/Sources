dnl $Id: ftest_util.m4,v 1.18 1998-04-06 11:30:51 schmidt Exp $
dnl
dnl ftest_util.m4 - m4 macros used by the factory test environment.
dnl
dnl "External" macro start with prefix `ftest', "internal" macros
dnl with prefix `_'.
dnl
dnl Almost all macros insert `#line'-preprocessor directives into
dnl code to aid debugging.
dnl
dnl Note: Be carefull where to place the ';'!
dnl
dnl do not output anything of this library
divert(-1)

#
# - internal macros.
#

#
# _stripTWS() - strip trailing white space from $1.
#
define(`_stripTWS', `dnl
patsubst(`$1', `[ 	]*$')')

#
# _qstripTWS() - strip trailing white space from $1, return
#   quoted result.
#
define(`_qstripTWS', `dnl
ifelse(
  translit(`$1', ` 	'), `', ,
  `patsubst(`$1', `\(.*[^ 	]\)[ 	]*$', ``\1'')')')


#
# - external macros.
#

#
# ftestSetNameOfGame() - set name of game.
#
# $1: name of algorithm
# $2: usage of algorithm
#
# These are stored in the macros `ftestAlgorithm' and
# `ftestUsage', resp.  Leaves notice on creator of this file.
#
define(`ftestSetNameOfGame', `dnl
define(`ftestAlgorithm',``$1'')dnl
define(`ftestUsage',``$2'')dnl
`/* This file was automatically generated by m4 using the ftest_util.m4 library */'')

#
# ftestPreprocInit() - initial preprocessor directives.
#
# In addition, change m4's comment character.  Change it in
# this place (and not earlier) because we want to replace
# `ftestAlgorithm' in the file-docu of the generated file.
#
define(`ftestPreprocInit', `dnl
changecom(`//')dnl
`#line' __line__ "__file__"
`#include <unistd.h>

#define TIMING
#include <timing.h>

#include <factory.h>

#include "ftest_util.h"
#include "ftest_io.h"'
dnl')

#
# ftestGlobalInit() - global initialization.
#
define(`ftestGlobalInit', `dnl
`#line' __line__ "__file__"
`TIMING_DEFINE_PRINT( ftestTimer )'')

#
# ftestMainInit() - initialization in main().
#
# Set the name of the game, check for missing arguments (in
# this case print the usage and exit), and catche signals.
#
define(`ftestMainInit', `dnl
`#line' __line__ "__file__"
    `int optind = 0;
    ftestStatusT check = UndefinedResult;

    ftestSetName( argv[0], "'ftestAlgorithm`", 'ftestUsage`);

    if ( argc == 1 ) {
        ftestUsagePrint();
        exit( 0 );
    }

    ftestSignalCatch();
    #line' __line__ "__file__"
dnl')

#
# ftestMainExit() - clean up in main().
#
define(`ftestMainExit', `dnl
`#line' __line__ "__file__"
    `return check'')

#
# ftestDefaultInitializer() - return type dependent default
#   initializer.
#
# $1: type
#
define(`ftestDefaultInitializer', `dnl
ifelse(
  `$1', `int', `` = 0'',
  `$1', `bool', `` = false'',
  `')')

#
# ftestOutVar() - declare output variable.
#
# $1: type of output variable
# $2: name of output variable
#
# Stores type of variable in macro _ftestOutType_<name>.  Does
# some extra magic for internal data types to avoid warnings on
# uninitialized variables.
#
define(`ftestOutVar', `dnl
define(`_ftestOutType_'_qstripTWS(`$2'), `$1')dnl
`$1 '_qstripTWS(`$2')ftestDefaultInitializer(`$1')')

#
# ftestInVar() - declare input variable.
#
# $1: type of input variable
# $2: name of input variable
#
# Stores type of variable in macro _ftestInType_<name>.
# Furthermore, declares a variable ftestArgGiven<name> for later
# checks whether this variable has been set from commandline or
# not.
# Does some extra magic for internal data types to avoid warnings
# on uninitialized variables.
#
define(`ftestInVar', `dnl
define(`_ftestInType_'_qstripTWS(`$2'), `$1')dnl
`$1 '_qstripTWS(`$2')ftestDefaultInitializer(`$1')`;
    bool ftestArgGiven$2= false'')

#
# ftestGetOpts() - read options.
#
define(`ftestGetOpts', `dnl
`#line' __line__ "__file__"
    `ftestGetOpts( argc, argv, optind )'')

#
# ftestGetEnv() - read environment.
#
# And print it directly after reading it.
#
define(`ftestGetEnv', `dnl
`#line' __line__ "__file__"
    `ftestGetEnv( argc, argv, optind );

    ftestPrintEnv();

'dnl')

#
# ftestGetInVar() - read variable from command line.
#
# $1: name of input variable
# $2: default for optional command line arguments
# $3: search for optional argument with this tag
#
# Before reading the argument, check whether it really exists.
# If so, call the appropriate function to convert the string into
# the type of the variable you are reading.  If there are not any
# more arguments, and there is no default specified, print an
# error.  If there is a default value, use it instead.
#
# If optional third argument is given, call
# `ftestSearchTaggedArg()' to check whether there is a tagged
# optional argument `<tag> = <value>' where `<tag>' is a
# substring of `$3'.  Use `<value>' as value for the input
# variable in this case, `$2' otherwise.
#
# In any case, save the fact whether the argument was given or
# not in the variable ftestArgGiven<name>.
#
define(`ftestGetInVar', `dnl
ifelse(
  `$#', `1',
  ``if ( argv[ optind ] ) {
        ftestArgGiven$1= true;
        ftestReadString( argv[ optind++ ], $1);
    } else
	ftestError( CommandlineError,
                    "expected '_stripTWS(`_ftestInType_$1')` at position %d in commandline\n",
                    optind );'',
  `$#', `2',
  ``if ( argv[ optind ] ) {
        ftestArgGiven$1= true;
        ftestReadString( argv[ optind++ ], $1 );
    } else
	$1 = '_qstripTWS(`$2')`;'',
  ``if ( ftestSearchTaggedArg( argc, argv, optind, $3) ) {
        ftestArgGiven$1 = true;
        ftestReadString( argv[ optind++ ], $1 );
    } else
	$1 = '_qstripTWS(`$2')`;'')
    `#line' __line__ "__file__"

dnl')

#
# ftestArgGiven() - check whether an argument was given.
#
# $1: name of input variable
#
define(`ftestArgGiven', `dnl
`ftestArgGiven'_qstripTWS(`$1')')

#
# ftestRun() - run test.
#
# $1: code to execute
#
# Do not forget to terminate the code to execute with a
# semicolon!
#
define(`ftestRun', `dnl
`#line' __line__ "__file__"
    `// check for superfluous command line arguments
    if ( argv[ optind ] )
	ftestError( CommandlineError, "superfluous argument `%s' at position %d",
                    argv[ optind ], optind );

    // save random generator seed now since the algorithm
    // most likely is going to change it
    ftestWriteSeed();

    if ( ftestAlarm )
	alarm( ftestAlarm );		// set alarm
    TIMING_START(ftestTimer);
    while ( ftestCircle > 0 ) {
	$1
	ftestCircle--;
    };
    TIMING_END(ftestTimer);
    if ( ftestAlarm )			// reset alarm
	alarm( 0 )'')

#
# ftestCheck() - run check.
#
# $1: check function (with parameters) to call
#
define(`ftestCheck', `dnl
`#line' __line__ "__file__"
    `if ( ftestCheckFlag )
	check = '_qstripTWS(`$1')')

#
# ftestOuput() - print results.
#
# Expands to code to print timer and check.  Then, for each
# argument pair `resultName, result', expands to print this
# pair.
#

# internal auxiliary function
define(`_ftestOutput', `dnl
ifelse(
  `$#', `0', ,
  `$#', `1', ,
``;
    ftestPrintResult( $1, '_qstripTWS(`$2')` )'_ftestOutput(shift(shift($@)))')')

define(`ftestOutput', `dnl
`#line' __line__ "__file__"
    `ftestPrintTimer( timing_ftestTimer_time );
    ftestPrintCheck( check )'_ftestOutput($@)')

dnl switch on output again
divert`'dnl
