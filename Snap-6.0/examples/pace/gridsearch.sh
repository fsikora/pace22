echo "TEMP ; ALPHA ; NBMV ; SCORE"
for TEMP in 0.2 0.3 0.5 0.6 ;
do
    for ALPHA in 0.9 0.99 ;
    do
        for NBMV in 2 5 10 15 ;
        do
            timeout 10s ./pace $TEMP $ALPHA $NBMV < ../../../heuristic_public/h_001 > sol
            SOLS=$(wc -l < sol)
            echo "$TEMP ; $ALPHA ; $NBMV ; $SOLS"
            #run timeout
            #wc -l
            #print
        done
    done
done