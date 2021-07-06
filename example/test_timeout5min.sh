# randltl -n50 a b c --output=aut
a=0
rm output/compare.log
rm output/verify.log
folder=ncsb_test/hoa
files=$(ls $folder)
for line in $files
do
    echo "File$a: $line"
    echo "File$a: $line" >> output/compare.log
    #ltl2tgba -f "$line" --output=ltlaut/aut$a.hoa
    #ltl2tgba --stats=%s -f "$line" >> output/compare.log
    if timeout 300s seminator --complement=spot ncsb_test/hoa/$line >> output/compare.log; then
        echo "spot $line success"
        autfilt spot/com.hoa --stats='spot states: %s; edges: %e' >> output/compare.log
    else 
        echo "spot timeout" 
        echo "spot timeout" >> output/compare.log
    fi

    if timeout 300s seminator --complement=pldi ncsb_test/hoa/$line >> output/compare.log; then
        echo "pldi $line success"
        autfilt pldi/com.hoa --stats='pldi states: %s; edges: %e' >> output/compare.log
    else 
        echo "pldi timeout" 
        echo "pldi timeout" >> output/compare.log 
    fi

    if timeout 300s seminator --complement=pldib ncsb_test/hoa/$line >> output/compare.log; then
        echo "pldib $line success"
        autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log
    else 
        echo "pldib timeout" 
        echo "pldib timeout" >> output/compare.log
    fi
    
    if timeout 300s autfilt ncsb_test/hoa/$line --complement -B --output=true/tcom$a.hoa; then
        echo "autfilt $line success"
        autfilt true/tcom$a.hoa --stats='autfilt state: %s; edges: %e' >> output/compare.log
    else 
        echo "autfilt timeout"
        echo "autfilt timeout" >> output/compare.log
    fi
    
    echo -e '\n'
    echo -e '\n' >> output/compare.log

    r="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results/re$a
    if $r >> results/re$a; then
	    echo "File$a: equivalent" >> output/verify.log
    else
	    echo "File$a: not equivalent" >> output/verify.log
    fi
    let a++
done 
