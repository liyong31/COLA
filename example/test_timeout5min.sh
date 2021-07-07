# randltl -n50 a b c --output=aut
a=0
rm output/compare.log
rm output/verify.log
folder=ba2hoa/difficult
files=$(ls $folder)
for line in $files
do
    echo "File$a: $line"
    echo "File$a: $line" >> output/compare.log
    #ltl2tgba -f "$line" --output=ltlaut/aut$a.hoa
    #ltl2tgba --stats=%s -f "$line" >> output/compare.log

    
    if timeout 300s autfilt ba2hoa/$line --complement -B --output=true/tcom$a.hoa; then
        echo "autfilt $line success"
        autfilt true/tcom$a.hoa --stats='autfilt state: %s; edges: %e' >> output/compare.log
    else 
        echo "File$a: autfilt timeout" >> output/verify.log
        echo "autfilt timeout"
        echo "autfilt timeout" >> output/compare.log
    fi
    
    if timeout 300s seminator --complement=spot ba2hoa/$line >> output/compare.log; then
        echo "spot $line success"
        autfilt spot/com.hoa --stats='spot states: %s; edges: %e' >> output/compare.log
    else 
        echo "File$a: spot timeout" >> output/verify.log
        echo "spot timeout" 
        echo "spot timeout" >> output/compare.log
    fi

    if timeout 300s seminator --complement=pldi ba2hoa/$line >> output/compare.log; then
        echo "pldi $line success"
        autfilt pldi/com.hoa --stats='pldi states: %s; edges: %e' >> output/compare.log
    else 
        echo "File$a: pldi timeout" >> output/verify.log
        echo "pldi timeout" 
        echo "pldi timeout" >> output/compare.log 
    fi

    if timeout 300s seminator --complement=pldib ba2hoa/$line >> output/compare.log; then
        echo "pldib $line success"
        autfilt pldib/com.hoa --stats='pldib states: %s; edges: %e' >> output/compare.log

        r1="autfilt true/tcom"$a".hoa --equivalent-to=pldib/com.hoa" # --output=results1/re$a
        if $r1 >> results1/re$a; then
	        echo "File$a: pldib equivalent" >> output/verify.log
        else
	        echo "File$a: pldib not equivalent" >> output/verify.log
        fi
    else 
        echo "File$a: pldib timeout" >> output/verify.log
        echo "pldib timeout"
        echo "pldib timeout" >> output/compare.log
    fi

    if timeout 300s seminator --complement=nsbc ba2hoa/$line >> output/compare.log; then
        echo "nsbc $line success"
        autfilt nsbc/com.hoa --stats='nsbc states: %s; edges: %e' >> output/compare.log
        r2="autfilt true/tcom"$a".hoa --equivalent-to=nsbc/com.hoa" # --output=results2/re$a
        if $r2 >> results2/re$a; then
	        echo "File$a: nsbc equivalent" >> output/verify.log
        else
	        echo "File$a: nsbc not equivalent" >> output/verify.log
        fi
    else 
        echo "File$a: nsbc timeout" >> output/verify.log
        echo "nsbc timeout"
        echo "nsbc timeout" >> output/compare.log
    fi

    echo -e '\n'
    echo -e '\n' >> output/compare.log
    

    let a++
done 
