# randltl -n50 a b c --output=aut
a=0
rm output/compare.log
rm output/verify.log
# folder=ba2hoa/difficultNormal 
#folder=ba2hoa/easy
folder=ncsb_test/hoa
files=$(ls $folder)
for line in $files
do
    echo "File$a: $line"
    echo "File$a: $line" >> output/compare.log
    #ltl2tgba -f "$line" --output=ltlaut/aut$a.hoa
    #ltl2tgba --stats=%s -f "$line" >> output/compare.log

    
    if timeout 900s autfilt $folder/$line --complement -B --output=true/tcom$a.hoa; then
        echo "autfilt $line success"
        autfilt true/tcom$a.hoa --stats='autfilt state: %s   edges: %e' >> output/compare.log
    else 
        echo "File$a: autfilt timeout" >> output/verify.log
        echo "autfilt timeout"
        echo "autfilt timeout" >> output/compare.log
    fi
    

    if timeout 900s seminator --complement=spot $folder/$line | grep -E "spot|Run time:" >> output/compare.log; then
        echo "spot $line success"
        # autfilt spot/com.hoa --stats='spot states: %s; edges: %e' >> output/compare.log
    else 
        echo "File$a: spot timeout" >> output/verify.log
        echo "spot timeout" 
        echo "spot timeout" >> output/compare.log
    fi


    if timeout 900s seminator --complement=pldi $folder/$line | grep -E "pldi|Run time:"  >> output/compare.log; then
        echo "pldi $line success"
        # autfilt pldi/com.hoa --stats='pldi states: %s; edges: %e' >> output/compare.log
    else 
        echo "File$a: pldi timeout" >> output/verify.log
        echo "pldi timeout" 
        echo "pldi timeout" >> output/compare.log 
    fi

    if timeout 900s seminator --complement=pldib $folder/$line | grep -E "pldib|Run time:" >> output/compare.log; then
        echo "pldib $line success"
        # autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log

        # r1="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results1/re$a
        # if $r1 >> results1/re$a; then
	    #     echo "File$a: pldib equivalent" >> output/verify.log
        # else
	    #     echo "File$a: pldib not equivalent" >> output/verify.log
        # fi
    else 
        echo "File$a: pldib timeout" >> output/verify.log
        echo "pldib timeout"
        echo "pldib timeout" >> output/compare.log
    fi

    #  if timeout 900s seminator --complement=pldif $folder/$line | grep -E "pldif|Run time:" >> output/compare.log; then
    #     echo "pldif $line success"
    #     # autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log

    #     # r1="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results1/re$a
    #     # if $r1 >> results1/re$a; then
	#     #     echo "File$a: pldib equivalent" >> output/verify.log
    #     # else
	#     #     echo "File$a: pldib not equivalent" >> output/verify.log
    #     # fi
    # else 
    #     echo "File$a: pldif timeout" >> output/verify.log
    #     echo "pldif timeout"
    #     echo "pldif timeout" >> output/compare.log
    # fi

    #  if timeout 900s seminator --complement=pldibf $folder/$line | grep -E "pldibf|Run time:" >> output/compare.log; then
    #     echo "pldibf $line success"
    #     # autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log

    #     # r1="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results1/re$a
    #     # if $r1 >> results1/re$a; then
	#     #     echo "File$a: pldib equivalent" >> output/verify.log
    #     # else
	#     #     echo "File$a: pldib not equivalent" >> output/verify.log
    #     # fi
    # else 
    #     echo "File$a: pldibf timeout" >> output/verify.log
    #     echo "pldibf timeout"
    #     echo "pldibf timeout" >> output/compare.log
    # fi

    if timeout 900s seminator --complement=nsbc $folder/$line | grep -E "nsbc|Run time:" >> output/compare.log; then
        echo "nsbc $line success"
        # autfilt nsbc/com.hoa --stats='nsbc states: %s; edges: %e' >> output/compare.log
        # r2="autfilt true/tcom"$a".hoa --equivalent-to=nsbc/com.hoa" # --output=results2/re$a
        # if $r2 >> results2/re$a; then
	    #     echo "File$a: nsbc equivalent" >> output/verify.log
        # else
	    #     echo "File$a: nsbc not equivalent" >> output/verify.log
        # fi
    else 
        echo "File$a: nsbc timeout" >> output/verify.log
        echo "nsbc timeout"
        echo "nsbc timeout" >> output/compare.log
    fi

    if timeout 900s java -jar ROLL.jar complement $folder/$line -ncsb | grep -E "#H.S|#H.T|#TTO" >> output/compare.log; then
        echo "roll $line success"
        # autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log

        # r1="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results1/re$a
        # if $r1 >> results1/re$a; then
	    #     echo "File$a: pldib equivalent" >> output/verify.log
        # else
	    #     echo "File$a: pldib not equivalent" >> output/verify.log
        # fi
    else 
        echo "File$a: roll timeout" >> output/verify.log
        echo "roll timeout"
        echo "roll timeout" >> output/compare.log
    fi

    echo -e '\n'
    echo -e '\n' >> output/compare.log
    

    let a++
done 
