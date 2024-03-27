import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
import subprocess

A = [[0 for i in range(256)] for i in range(8)]
result=0
def Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum,MinGEC):
    countA = 0
    countB = 0
    countQ = 0
    countT = 0
    countX = 0
    countY = 0
    for k in range(GateNum):
        # Q
        for q in range(4):
            fout.write("ASSERT(  Q_" + str(countQ) + " = ")
            for i in range(bitnum):
                x = "A_" + str(countA) + " & X_" + str(i)
                if (k == 0 and i == bitnum - 1):
                    fout.write(x)
                else:
                    fout.write("BVXOR( " + x + ", ")
                countA += 1
            for i in range(countT):
                x = "A_" + str(countA) + " & T_" + str(i)
                if (i == countT - 1):
                    fout.write(x)
                else:
                    fout.write("BVXOR( " + x + ", ")
                countA += 1
            for i in range(bitnum + countT):
                if (i == bitnum + countT - 1):
                    fout.write(" );\n")
                else:
                    fout.write(" )")
            countQ += 1

        xx0 = "0bin"
        xx1 = "0bin"
        for j in range(Size):
            xx0 = xx0 + "0"
            xx1 = xx1 + "1"
        fout.write("ASSERT( T_" + str(countT) + " = BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 4) +
                   " & Q_" + str(countQ - 3) + " & Q_" + str(countQ - 2) + " & Q_" + str(countQ - 1)
                   + " , BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 4) + " & Q_" + str(
            countQ - 3) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 4) + " & Q_" + str(
            countQ - 3) + " & Q_" + str(countQ - 1)
                   + " , BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 2) + " & Q_" + str(countQ - 1)
                   + " , BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 1)
                   + " , BVXOR( B_" + str(countB + 1) + " & Q_" + str(countQ - 4) + " & Q_" + str(
            countQ - 3) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 4) + " & Q_" + str(countQ - 3)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 4) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 3) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 4)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 3)
                   + " , BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB + 3) + " & Q_" + str(countQ - 4)
                   + " , BVXOR( B_" + str(countB + 3) + " & Q_" + str(countQ - 3)
                   + " , BVXOR( B_" + str(countB + 3) + " & Q_" + str(countQ - 2)
                   + " , BVXOR( B_" + str(countB + 4) + " & Q_" + str(countQ - 4) + " & Q_" + str(countQ - 3)
                   + " , BVXOR( B_" + str(countB + 5) + " & Q_" + str(countQ - 4)
                   + " , BVXOR( B_" + str(countB + 5) + " & Q_" + str(countQ - 3)
                   + " , BVXOR( B_" + str(countB + 6) + " & Q_" + str(countQ - 4)
                   + " , B_" + str(countB + 7)
                   + ") ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ;\n")
        countB += 8
        countT += 1
    # Y
    for y in range(bitnum):
        fout.write("ASSERT( Y_" + str(y) + " = ")
        for i in range(bitnum):
            x = " A_" + str(countA) + " & X_" + str(i)
            fout.write("BVXOR( " + x + ",")
            countA += 1
        for i in range(GateNum):
            x = " A_" + str(countA) + " & T_" + str(i)
            if (i == GateNum - 1):
                fout.write(x)
            else:
                fout.write("BVXOR( " + x + ",")
            countA += 1
        for i in range(bitnum + countT):
            if (i == bitnum + countT - 1):
                fout.write(" );\n")
            else:
                fout.write(" )")
    for i in range(GateNum):
        fout.write("ASSERT( C_" + str(i) + " = Cost[B_" + str(8 * i) + "[0:0]@B_" + str(8 * i + 1) + "[0:0]@B_" + str(
            8 * i + 2) + "[0:0]@B_" +
                   str(8 * i + 3) + "[0:0]@B_" + str(8 * i + 4) + "[0:0]@B_" + str(8 * i + 5) + "[0:0]@B_" + str(
            8 * i + 6) + "[0:0]@B_" + str(8 * i + 7) + "[0:0]] );\n")
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

if __name__ == '__main__':
    Cipherstr = "PROST"
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST
    BGC = 8  # number of gates
    bitnum = 4
    GEC=37
    for GateNum in range(BGC,1,-1):
        Size = pow(2, bitnum)
        QNum = 4 * GateNum
        aNum = 4 * (2 * bitnum + GateNum - 1) * GateNum // 2 + bitnum * bitnum + GateNum * bitnum
        bNum = 8*GateNum
        MinGEC=GEC
        if not os.path.exists("./oldgec"):
            os.system("mkdir ./oldgec")
        if not os.path.exists("./oldgec/" + Cipherstr):
            os.system("mkdir ./oldgec/" + Cipherstr)
        filestr = "./oldgec/"+Cipherstr+"/"+Cipherstr+"oldge"
        fout=open(filestr + ".cvc", 'w')
        State_Variate(fout, bitnum, Size, GateNum, QNum, bNum,aNum)
        Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, Sbox)
        Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum,MinGEC)
        Objective(fout)
        fout.close()
        # start---------------
        tttstr=[]
        x = 1
        order = "stp -p " + str(filestr) + ".cvc"  # > "+file+".txt "
        # print(order)
        start_time = time.time()
        # print(i,start_time)
        # s=(os.popen(order))
        # os.system(order)
        s = (os.popen(order).read())
        resultstr = s
        print(s)

