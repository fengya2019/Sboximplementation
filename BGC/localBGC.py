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
                    order = "stp -p " + str(filestr) + ".cvc "  # > "+file+".txt "
                    #print(order)
                    start_time = time.time()
                    # print(i,start_time)
                    # s=(os.popen(order))
                    # os.system(order)
                    s = (os.popen(order).read())
                    resultstr = s
                    print(s,filestr)
