import os, re  

# execute command, and return the output  
def execCmd(cmd):  
    r = os.popen(cmd)  
    text = r.read()  
    r.close()  
    return text  

# write "data" to file-filename  
def writeFile(filename, data):  
    f = open(filename, "w")  
    f.write(data)  
    f.close()  


if __name__ == '__main__':  
    
    k = 0
    for line in open("random_nd.ltl"): 
        cmdLtl2tgba = "ltl2tgba -f \"" + line + "\" --output=ltlaut/aut" + str(k) + ".hoa"  
        cmdSpot = "seminator --complement=spot ltlaut/aut" + str(k) + ".hoa"
        cmdPldi = "seminator --complement=pldi ltlaut/aut" + str(k) + ".hoa"
        cmdNsbc = "seminator --complement=nsbc ltlaut/aut" + str(k) + ".hoa"
        cmdAutfiltCom = "autfilt ltlaut/aut" + str(k) + ".hoa --complement --output=true/tcom" + str(k) + ".hoa"
        cmdAutfiltEquiv = "autfilt spot/com.hoa --equivalent-to=nsbc/com.hoa --output=results/re" + str(k)
        
        execCmd(cmdLtl2tgba)
        execCmd(cmdSpot)
        execCmd(cmdPldi)
        execCmd(cmdNsbc)
        execCmd(cmdAutfiltCom)
        execCmd(cmdAutfiltEquiv)
        k = k+1
    # result = execCmd(cmd)  
    # pat1 = "Physical Address[\. ]+: ([\w-]+)"  
    # pat2 = "IP Address[\. ]+: ([\.\d]+)"  
    # MAC = re.findall(pat1, result)[0]       # 找到MAC  
    # IP = re.findall(pat2, result)[0]        # 找到IP  
    # print("MAC=%s, IP=%s" %(MAC, IP)) 
