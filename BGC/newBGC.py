import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
result =0
A = [[0 for i in range(256)] for i in range(8)]
resstr = ""

def State_Variate(fout, bitnum, Size, GateNum, QNum, bNum):
    # State Variate
    for i in range(bitnum):
        fout.write('X_' + str(i))
        if (i == bitnum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    for i in range(bitnum):
        fout.write("Y_" + str(i))
        if (i == bitnum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    for t in range(GateNum):
        fout.write("T_" + str(t))
        if (t == GateNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    for i in range(QNum):
        fout.write("Q_" + str(i))
        if (i == QNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    for i in range(bNum):
        fout.write("B_" + str(i))
        if (i == bNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")


def Decompose(flag, Sbox):
    for i in range(Size):
        tem = ""
        if flag == 0:
            tem = i
        else:
            tem = Sbox[i]
        for j in range(bitnum - 1, -1, -1):
            A[j][i] = tem % 2
            tem //= 2


def Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, Sbox):
    # Trival Constraints
    # X
    Decompose(0, Sbox)
    for i in range(bitnum):
        fout.write("ASSERT( X_" + str(i) + " = 0bin")
        for j in range(Size):
            fout.write(str(A[i][j]))
        fout.write(" );\n")
    #B
    for i in range(0, bNum):
        x0 = "0bin0"        
        fout.write("ASSERT( B_" + str(i) + "[2:2] & B_" + str(i) + "[0:0] = " + x0 + "  );\n")
    #for i in range(0, bNum,2):
    #    fout.write("ASSERT( BVGT(Q_" + str(i) + ", Q_" + str(i + 1) + "));\n")


def Logic_SubConstraint(fout, bitnum, Size, GateNum, Qsum, Tsum, depth, p):
    countQ = Qsum
    countT = Tsum
    for k in range(GateNum):
        # Encoding Q
        for q in range(2):
            if depth == 0 or q == 0 or p==0:
                fout.write("ASSERT( ")
                for i in range(bitnum):
                    fout.write("( Q_" + str(countQ) + " = X_" + str(i) + ")")
                    if (depth == 0 and i == bitnum - 1):
                        fout.write(" );\n")
                    else:
                        fout.write(" OR ")

                for i in range(Tsum):
                    fout.write("( Q_" + str(countQ) + " = T_" + str(i) + ")")
                    if (i == Tsum - 1):
                        fout.write(" );\n")
                    else:
                        fout.write(" OR ")
                countQ = countQ + 1
            else:
                fout.write("ASSERT( ")
                for i in range(Tsum):
                    fout.write("( Q_" + str(countQ) + " = T_" + str(i) + ")")
                    if (i == Tsum - 1):
                        fout.write(" );\n")
                    else:
                        fout.write(" OR ")
                countQ = countQ + 1
        xx0 = "0bin"
        xx1 = "0bin"
        for j in range(Size):
            xx0 = xx0 + "0"
            xx1 = xx1 + "1"
        # encoding T
        #fout.write(
        #    "ASSERT( BVGT(T_" + str(countT)+","+xx0+"));\n")
        #for t in range(0,countT):
        #    fout.write(
        #    "ASSERT( NOT(T_" + str(countT)+" = T_"+str(t)+"));\n")
        fout.write(
            "ASSERT( T_" + str(countT) + " = BVXOR((IF B_" + str(countT) + "[2:2] =0bin1 THEN Q_" + str(
                countQ - 2) + " & Q_" + str(
                countQ - 1) +
            " ELSE " + xx0 + " ENDIF), BVXOR((IF B_" + str(countT) + "[0:0]=0bin1 THEN ~Q_" + str(
                countQ - 2) + " ELSE " + xx0 + " ENDIF), (IF B_" + str(
                countT) + "[1:1]=0bin1 THEN BVXOR( Q_" + str(countQ - 2) + ",  Q_" + str(
                countQ - 1) + ") ELSE " + xx0 + " ENDIF ) ) ) ); \n")
        countT += 1


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
    order = ""
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
                                

