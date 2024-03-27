import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
result =0
A = [[0 for i in range(256)] for i in range(8)]
resstr = ""

def tobits(num, bit_len):
    # tobinary string
    res = ""
    for pos in range(bit_len):
        res = str(num % 2) + res
        num /= 2
    return res


def Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, depth,SS,p):
    countB = 0
    countQ = 0
    countT = 0
    lenght = bitnum
    for d in range(depth):
        # print(d,countT)
        Logic_SubConstraint(fout, bitnum, Size, SS[d], countQ, countT, d,p)
        countQ = countQ + 2 * SS[d]
        countT = countT + SS[d]
        # print(lenght)
        # Y
    #    // encoding Y
    for y in range(bitnum):
        fout.write("ASSERT( ")
        for i in range(GateNum):
            fout.write("( Y_" + str(y) + " =  T_" + str(i))
            if (i == GateNum - 1):
                fout.write("));\n")
            else:
                fout.write(" ) OR ")



def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")

def thread_func(threads, filestr,i):
    global result
    order = "stp -p " + str(filestr) + ".cvc --cryptominisat --threads 1"# > " + filestr + ".txt "
    # print(order)
    start_time = time.time()
    # print(i,start_time)
    s=(os.popen(order).read())
    #os.system(order)
    end_time = time.time()
    print(s)
    result=i
    if "Invalid." in s:
        print(i,filestr, (end_time - start_time) * 1000, 'ms')
        fouts = open(filestr + "Yes.txt", 'a+')
        fouts.write(str(s))
        fouts.write(str(i) + str((end_time - start_time) * 1000))
        fouts.close()
    elif "Valid." in s:
        print(i,filestr, (end_time - start_time) * 1000, 'ms')
        fouts = open(filestr + "No.txt", 'a+')
        fouts.write(str(s))
        fouts.write(str(i) + str((end_time - start_time) * 1000))
        fouts.close()

def combination_impl(l, n, stack,length,SS):
    if n == 0:
        if len(stack)==length:
            ss=[]
            for i in range(len(stack)):
                ss.append(stack[i])
            #print(ss)
            SS.append(ss)
        return
    for i in range(0, len(l)):
        if l[i] <= n:
            stack.append(l[i])
            combination_impl(l, n - l[i], stack,length,SS)
            stack.pop()
        else:
            break

if __name__ == '__main__':
    result = 0
    Cipherstr = "PROST"
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST
    BGC = 8#number of gates
    bitnum = 4 #4
    d=2 #depth
    p=0#parallel sign

    for GateNum in range(BGC, 1,-1):
        result=0
        Size = pow(2, bitnum)
        QNum = 2 * GateNum
        bNum = GateNum
        l = []
        for j in range(1, GateNum + 1):
            l.append(j)
        tttstr=[]
        stardepth = GateNum
        enddepth = GateNum-1
        if p:#parallel implementation
            stardepth=d
            enddepth=1
        for depth in range(stardepth, enddepth,-1):
            SStr = []
            combination_impl(l, GateNum, [], depth, SStr)
            SStr0=[]
            for dd in range(len(SStr)):
                SS = SStr[len(SStr) - dd - 1]
                ff=1
                gs=bitnum
                g0=0
                for sd in range(len(SS)):
                    if SS[len(SS)-sd-1]>gs+g0:
                        ff=0
                        break
                    g0=g0+gs-SS[len(SS)-sd-1]
                    gs=2*SS[len(SS)-sd-1]
                if(ff):
                    SStr0.append(SS)
            x=1
            val=1
            ishassolver=0
            for d in range(len(SStr0)):
                result=0
                SS=SStr0[d]
                sz=""
                for dd in range(len(SS)):
                    sz=sz+str(SS[dd])
                print(d,Cipherstr,SS)
                if not os.path.exists("./bgc"):
                    os.system("mkdir ./bgc")
                if not os.path.exists("./bgc/" + Cipherstr):
                    os.system("mkdir ./bgc/" + Cipherstr)
                filestr = "./bgc/"+Cipherstr+"/newbgc"+str(GateNum)+sz
                fout = open(filestr + "0.cvc", 'w')
                print(filestr)
                State_Variate(fout, bitnum, Size, GateNum, QNum, bNum)#define Variate X, Y, B, T, Q
                Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, Sbox)#Constraints of X, Y B, T, Q
                Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, depth,SS,p) #Encoding of gates' inputs and outputs, S-box outputs
                Objective(fout)
                fout.close()
                fout0 = open(filestr + "1.cvc", 'w')
                fout1 = open(filestr + "2.cvc", 'w')
                # fout2=open(filestr + ".txt", 'w')
                b0str = ""
                b1str = ""
                for j in range(0, QNum, 2):
                    b0str = b0str + "ASSERT( BVGT(Q_" + str(j) + ", Q_" + str(j + 1) + "));\n"
                    b1str = b1str + "ASSERT( BVGT(Q_" + str(j + 1) + ", Q_" + str(j) + "));\n"
                lines0 = []
                lines = []
                f = open(filestr + "0.cvc", 'r')
                s = ""
                s0 = ""
                for line in f:
                    lines.append(line)
                    lines0.append(line)
                lines0.insert(5 + 2 * bitnum + 2 * GateNum, b0str)
                lines.insert(5 + 2 * bitnum + 2 * GateNum, b1str)
                s = ''.join(lines)
                s0 = ''.join(lines0)
                fout0.write(s0)
                f.close()
                # fout0=open(filestr + ".cvc", 'w')
                fout1.write(s)
                fout0.close()
                fout1.close()
                # fout2.close()
                # start---------------
                # time.sleep(1)
                resstr = ""
                threads = []
                # thread_func(filestr,filestr)
                for j in range(0, 3):
                    p = threading.Thread(target=thread_func, args=(threads, str(filestr) + str(j),d,))
                    threads.append(p)
                # print(threads)
                # p.start()

                result=0

                for t in threads:
                    t.start()#
                x = 1
                while (x):
                    #xx=0
                    #end_time = time.time()
                    #if end_time - start_time > 600:#time limit
                    #    xx=1
                    if result == d:  # len(cipher):
                        x = 0
                        order = "ps -ef|grep " + Cipherstr
                        res = os.popen(order).read()
                        for line in res.splitlines():
                            s = line.split()
                            if filestr+"0.cvc" in s or filestr+"1.cvc" in s or filestr+"2.cvc" in s:
                                r = os.popen("kill -9 " + s[1]).read()
                                

