#!/bin/sh

# -o maven flags force offline mode so dependencies are cached.

# 1x parallelism: run everything on a single container.
ONE_PARALLEL="mvn test -o -Dgpg.skip"

# 2x parallelism: isolate very slow tests for container 1, everything else on container 2.
TWO_PARALLEL_C1="mvn test -o -pl module-check -Dgpg.skip"
TWO_PARALLEL_C2="mvn test -o -pl module-rt -Dgpg.skip"

case $CIRCLE_NODE_TOTAL in
 1) # 1x parallelism
    echo "Detected 1x parallelism."
    echo $ONE_PARALLEL
    eval $ONE_PARALLEL
		;;
 2)
    echo "Detected 2x parallelism, utilizing 2 containers."
    case $CIRCLE_NODE_INDEX in 
      0) echo $TWO_PARALLEL_C1
         eval $TWO_PARALLEL_C1
         ;; 
      1) echo $TWO_PARALLEL_C2
         eval $TWO_PARALLEL_C2
         ;; 
      *) echo "Inconsistent state"
         exit 1 ;;
    esac
		;;
 *) echo "Detected #{CIRCLE_NODE_TOTAL} parallelism, too much parallelism. Running full suite."
    echo $ONE_PARALLEL
    eval $ONE_PARALLEL
		;;
esac

# Forward exit code from tests.
exit $?
