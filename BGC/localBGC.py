import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
import subprocess
from itertools import combinations

A = [[0 for i in range(256)] for j in range(8)]
result=0

def State_Variate(fout, bitnum, Size, GateNum, QNum, bNum,yN,TTstr):
    #State Variate
    #x
    for i in range(bitnum):
        fout.write('X_' + str(i))
        if (i == bitnum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    #y
    for i in range(yN):
        fout.write("Y_" + str(i))
        if (i == yN - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    #t
    for t in range(GateNum+len(TTstr)):
        fout.write("T_"+ str(t))
        if (t == GateNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    #q
    for i in range(QNum):
        fout.write("Q_"+ str(i))
        if (i == QNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")
    #B
    for i in range(bNum):
        fout.write("B_" + str(i))
        if (i == bNum - 1):
            fout.write(" : BITVECTOR( " + str(Size) + " );\n")
        else:
            fout.write(" , ")

def Decompose(flag,Sbox):
    #get value of X or Y
    for i in range(Size):
        tem = ""
        if flag == 0:
            tem = i
        else:
            tem = Sbox[i]
        for j in range(bitnum - 1, -1, -1):
            A[j][i] = tem % 2
            tem //= 2


def Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum,Sbox,yN,Yelem,constr):
    # Trival Constraints
    # X
    Decompose(0,Sbox)
    for i in range(bitnum):
        fout.write("ASSERT( X_" + str(i) + " = 0bin")
        for j in range(Size):
            fout.write(str(A[i][j]))
        fout.write(" );\n")
    # Y
    Decompose(1,Sbox)
    for i in range(yN):
        fout.write("ASSERT( Y_" + str(i) + " = 0bin")
        for j in range(Size):
            fout.write(str(A[Yelem[i]][j]))
        fout.write(" );\n")
    #B
    for i in range(0, bNum):
        x0 = "0bin0"
        fout.write("ASSERT( B_" + str(i) + "[2:2] & B_" + str(i) + "[0:0] = " + x0 + "  );\n")
        fout.write("ASSERT( B_" + str(i) + "[1:1] & B_" + str(i) + "[0:0] = " + x0 + "  );\n")
    #Q
    for i in range(0, QNum, 2):
        fout.write("ASSERT( BVGE(Q_" + str(i) + ", Q_" + str(i + 1) + "));\n")

    for i in range(len(constr)):
        fout.write(constr[i])


def Logic_SubConstraint(fout, bitnum, Size, GateNum, Qsum, Tsum, depth,p):
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


def Logic_Constraint(fout, bitnum, Size, GateNum, depth,SS,yN,p):
    countB = 0
    countQ = 0
    countT = 0
    lenght = bitnum
    for d in range(depth):
        # print(d,countT)
        Logic_SubConstraint(fout, bitnum, Size, SS[d], countQ, countT, d, p)
        countQ = countQ + 2 * SS[d]
        countT = countT + SS[d]
        lenght = lenght + SS[d]
        # print(lenght)
        # Y
    #    // encoding Y
    for y in range(yN):
        fout.write("ASSERT( ")
        for i in range(GateNum):
            fout.write("( Y_" + str(y) + " =  T_" + str(i))
            if (i == GateNum - 1):
                fout.write("));\n")
            else:
                fout.write(" ) OR ")


def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")


def thread_func(t,filestr, strs):
    global result
    order = "stp -p " + str(filestr) + ".cvc --cryptominisat --threads 1"# > " + file + ".txt "
    # print(order)
    start_time = time.time()
    # print(i,start_time)
    s=(os.popen(order).read())
    #os.system(order)
    end_time = time.time()
    # for t in threads:
    #    if
    # print(file,(end_time-start_time)*1000,'ms')

    if "Invalid." in s:
        result =strs
        print(s,filestr, strs,(end_time-start_time)*1000,'ms')
        fouts=open(filestr+"Y.txt",'a+')
        fouts.write(str(s))
        fouts.write(str((end_time - start_time)*1000))
        fouts.close()
    elif "Valid." in s:        
        result =strs
        print(s,filestr, strs,(end_time-start_time)*1000,'ms')
        fouts=open(filestr+"N.txt",'a+')
        fouts.write(str(s))
        fouts.write(str((end_time - start_time)*1000))
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
    n0=1 #part of S-box outputs
    yystr=[] #the part of S-box output with solution if Y_2,Y_3 has solution, yystr=[2,3]

    TTstr=[] #the solution of part S-box output, its value is [T_0,T_1...]

    constr=[]#Exclude existing solutions realized by S-box NOT(T_0=0xf22f)
    Cipherstr = "PROST"#ciphername
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # #S-box
    BGC = 8  # number of gates n0 or n1
    bitnum = 4  #number of S-box inputs
    d = 2  # depth
    p=0#parallel sign
    for GateNum in range(BGC,1,-1):
        result =0
        items=[] #part of S-box output without solution
        Size = pow(2, bitnum)#2^n length
        QNum = 2 * GateNum #total number of 2-input gates' inputs
        bNum = GateNum  #number of variate B
        yy=[]
        l=[]
        for j in range(1, GateNum + 1):
            l.append(j)
        for y in range(bitnum):
            if y not in yystr:
                items.append(y)
        for c in combinations(items, n0): #Obtain any n0 outputs of S-box
            yy.append(c)

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
                gs=n0
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
            issolver=0
            for d in range(len(SStr0)):
                result=0
                SS=SStr0[d]
                for y0 in range(len(yy)):  #Encoding and solve any n outputs of S-box using thread
                    strz=""
                    for yy0 in range(len(yy[y0])):
                        strz=strz+str(yy[y0][yy0])
                    print(d,Cipherstr,SS)
                    if not os.path.exists("./localbgc"):
                        os.system("mkdir ./localbgc")
                    if not os.path.exists("./localbgc/"+Cipherstr):
                        os.system("mkdir ./localbgc/"+Cipherstr)
                    if not os.path.exists("./localbgc/"+Cipherstr+"/11"):
                        os.system("mkdir ./localbgc/"+Cipherstr+"/11")
                    filestr = "./localbgc/"+Cipherstr+"/11/"+Cipherstr+"LocalBGC"+str(GateNum)+strz #encoding modle to file
                    fout=open(filestr + ".cvc", 'w')
                    State_Variate(fout, bitnum, Size, GateNum, QNum, bNum,n0,TTstr)  #define Variate X, Y, B, T, Q
                    Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, Sbox,n0,yy[y0],constr) #Constraints of X, Y, B, T, Q
                    Logic_Constraint(fout, bitnum, Size, GateNum, depth,SS,n0,p) #Encoding of gates' inputs and outputs, S-box outputs
                    Objective(fout)
                    fout.close()
                    tttstr=[]
                    x=1
                    xx=0
                    while (x):
                        order = ""
                        #print(order)
                        start_time = time.time()
                        # print(i,start_time)
                        # s=(os.popen(order))
                        # os.system(order)
                        s = (os.popen(order).read())
                        resultstr = s
                        print(s,filestr)
                        if "Invalid." in s:
                            issolver=1
                            Astr = []
                            AAstr = []
                            Ystr = ""
                            for line in resultstr.splitlines():
                                s0 = line.split()
                                if "Y_" in s0[1]:
                                    Ystr = int(s0[3], 16)
                                    break
                            ttstr = []
                            for line in resultstr.splitlines():
                                s0 = line.split()
                                isture = 0
                                print(s0)
                                if len(s0) > 2 and "T_" in s0[1] and int(s0[3], 16) != Ystr:
                                    Astr.append("".join(s0))
                                    ttstr.append(int(s0[3], 16))
                                if len(s0) > 2 and "T_" in s0[1]:
                                    AAstr.append("".join(s0))
                            fstr = "./localbgc/"+Cipherstr+"/11/" + Cipherstr+str(GateNum)+strz +str(depth)
                            foutc = open(fstr + ".txt", 'a+')
                            foutc.write(s)
                            foutc.close()
                            if len(Astr) > 0:
                                ttstr.sort()
                                if ttstr not in tttstr:
                                    filestr1 = "./localbgc/"+Cipherstr+"/11/" + str(GateNum)+strz  +str(depth)
                                    fout1 = open(filestr1 + ".txt", 'a+')
                                    fout1.write("\n".join(AAstr) + "\n\n")
                                    fout1.close()
                                    tttstr.append(ttstr)
                                f = open(filestr + ".cvc", 'r')
                                lines = []
                                b1str = "ASSERT("
                                for i0 in range(len(Astr)):
                                    b1str = b1str + " (NOT" + ((Astr[i0].replace("ASSERT", "")).replace(";", "")) + ") "
                                    if i0 == len(Astr) - 1:
                                        b1str = b1str + ");\n"
                                    else:
                                        b1str = b1str + "AND"
                                # print(b1str)
                                for line in f:
                                    lines.append(line)
                                lines.insert(4 + 2 * bitnum + GateNum, b1str)
                                s = ''.join(lines)
                                f.close()
                                f = open(filestr + ".cvc", 'w')
                                f.write(s)
                                f.close()
                        else:
                            filestr = "./localbgc/"+Cipherstr+"/11/"+Cipherstr+"LocalBGC"+str(GateNum)+strz #encoding modle to file
                            os.system("rm -f "+ filestr+".cvc")
                            x=0
                            xx=1
                if issolver:
                    break
