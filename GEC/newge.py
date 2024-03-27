import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
import subprocess
from itertools import combinations
resultstr=0
result = 0
A = [[0 for i in range(256)] for i in range(8)]

cost = [
    ["0bin00001000", "0bin00000110",
     "0bin00000100", "0bin00000011",
     "0bin00000100", "0bin00000011",
     "0bin00000010", "0bin00000010",
     "0bin00000010", "0bin00001110",
     "0bin00001110", "0bin00000110",
     "0bin00000100", "0bin00000110",
     "0bin00000100", "0bin00001000",
     "0bin00000110"],
    ["0bin00001000", "0bin00001000",
     "0bin00000101", "0bin00000011",
     "0bin00000101", "0bin00000011",
     "0bin00000011", "0bin00000011",
     "0bin00000011", "0bin00010010",
     "0bin00010011", "0bin00000110",
     "0bin00000110", "0bin00000110",
     "0bin00000110", "0bin00001000",
     "0bin00001000"]
]  # the GE of different library
Gatetype=["XOR","XNOR", "AND", "NAND", "OR", "NOR", "NOT", "NOT", "NOT", "XOR3", "XNOR3",
          "AND3", "NAND3", "OR3", "NOR3", "MAOI1", "MOAI1"]
GateVal=["0bin00000010","0bin00000011","0bin00000100","0bin00000101","0bin00000110",
         "0bin00000111","0bin00001001","0bin00001011","0bin00010001","0bin00010010",
         "0bin00010011","0bin00100000","0bin00100001","0bin01110110","0bin01110111",
         "0bin10110000","0bin10110001"]
def Logic_Constraint(fout, bitnum, Size, GateNum, MinGEC, depth, SS):
    countB = 0
    countQ = 0
    countT = 0
    for d in range(depth):
        Logic_SubConstraint(fout, bitnum, Size, SS[d], countQ, countT, d, countB)
        countQ = countQ + 4 * SS[d]
        countT = countT + SS[d]
        countB = countB + SS[d]
    # Y
    for y in range(bitnum):
        fout.write("ASSERT( ")
        for i in range(GateNum):
            fout.write("( Y_" + str(y) + " =  T_" + str(i))
            if (i == GateNum - 1):
                fout.write("));\n")
            else:
                fout.write(" ) OR ")
    for i in range(GateNum):
        fout.write("ASSERT( C_" + str(i) + " = Cost[ B_" + str(i) + "] );\n")

    for i in range(GateNum):
        if (i == 0):
            fout.write("ASSERT( GEC = BVPLUS( 8 , ")
        fout.write("C_" + str(i))
        if (i == GateNum - 1):
            fout.write(" ) );\n")
        else:
            fout.write(" , ")
    fout.write("ASSERT( BVLT(GEC , 0bin" + tobits(MinGEC, 8) + ") );\n")


def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")


def thread_func(threads, file):
    global result
    global resultstr
    order = "stp -p " + str(file) + ".cvc --cryptominisat --threads 1 > " + file + ".txt "
    start_time = time.time()
    s = (os.popen(order).read())
    print(s)
    resultstr = s
    end_time = time.time()

    if result == 0:
        result = 1
        fouts = open(filestr + ".txt", 'w')
        resultstr=s
        fouts.write(s)
        fouts.write("time:" + str((end_time - start_time) * 1000))
        fouts.close()


def combination_impl(l, n, stack, length, SS):
    if n == 0:
        if len(stack) == length:
            ss = []
            for i in range(len(stack)):
                ss.append(stack[i])
            SS.append(ss)
        return
    for i in range(0, len(l)):
        if l[i] <= n:
            stack.append(l[i])
            combination_impl(l, n - l[i], stack, length, SS)
            stack.pop()
        else:
            break


if __name__ == '__main__':
    Cipherstr = "PROST"
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST
    GN = 8  # number of gates
    GEC = 37  # number of gates
    bitnum = 4
    lg=[]
    scl = 1
    dup=4
    dsign=1 #depth
    for GateNum in range(GN,1,-1):
        Size = pow(2, bitnum)
        QNum = 4 * GateNum
        bNum = GateNum
        MinGEC = GEC
        l = []
        tttstr = []
        stardepth = GateNum
        if dsign:  # parallel implementation
            stardepth = dup
        for j in range(1, GateNum + 1):
            l.append(j)
        for depth in range(stardepth, 1, -1):
            SStr = []
            combination_impl(l, GateNum, [], depth, SStr)
            SStr0 = []
            for dd in range(len(SStr)):
                SS = SStr[dd]
                ff = 1
                gs = bitnum
                gx = 0
                for sd in range(len(SS)):
                    if SS[len(SS) - sd - 1] > gs + gx:
                        ff = 0
                        break
                    gx = gs + gx - SS[len(SS) - sd - 1]
                    gs = 2 * SS[len(SS) - sd - 1]
                if (ff):
                    SStr0.append(SS)
            ishassolver = 0
            for d in range(len(SStr0)):
                SS=SStr0[d]
                if not os.path.exists("./gec"):
                    os.system("mkdir ./gec")
                if not os.path.exists("./gec/" + Cipherstr):
                    os.system("mkdir ./gec/" + Cipherstr)

                filestr = "./gec/"+Cipherstr+"/"+Cipherstr+"gec"  #encoding modle to file
                fout = open(filestr + "0.cvc", 'w')
                State_Variate(fout, bitnum, Size, GateNum, QNum, scl)
                Trival_Constraint(fout, bitnum, Size, GateNum, Sbox,lg)
                Logic_Constraint(fout, bitnum, Size, GateNum, MinGEC, depth, SS)
                Objective(fout)
                fout.close()
                x = 1
                order = "stp -p " + str(filestr) + ".cvc  --cryptominisat --threads 1"  # > "+file+".txt "
                # print(order)
                start_time = time.time()
                # print(i,start_time)
                # s=(os.popen(order))
                # os.system(order)
                s = (os.popen(order).read())
                resultstr = s
                print(s)
