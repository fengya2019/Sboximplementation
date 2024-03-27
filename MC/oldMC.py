import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
A = [[0 for i in range(256)] for j in range(8)]

resstr = ""
def Logic_Constraint(fout, bitnum, GateNum):
    countA = 0
    countQ = 0
    countT = 0
    for k in range(GateNum):
        # Q
        for q in range(2):
            # encoding Q, input of gates
            fout.write("ASSERT(  Q_" + str(countQ) + " = ")
            for i in range(bitnum + 1):
                x = ""
                if i == 0:
                    x = "A_" + str(countA)
                else:
                    x = "A_" + str(countA) + " & X_" + str(i - 1)
                if (k == 0 and i == bitnum):
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
            for i in range(bitnum + countT + 1):
                if (i == bitnum + countT):
                    fout.write(" );\n")
                else:
                    fout.write(" )")
            countQ += 1

        # T encoding output of gates
        fout.write("ASSERT( T_" + str(countT) + " = Q_" + str(countQ - 2) + " & Q_" + str(countQ - 1) + " ); \n")
        countT += 1
    # Y  encoding output of S-box
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


def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")


if __name__ == '__main__':
    Cipherstr = "PROST"# ciphername
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST# S-box
    MC = 8  # number of AND gates
    bitnum = 4# number of S-box inputs
    for GateNum in range(MC,1,-1):
        Size = pow(2, bitnum)  # 2^n length
        QNum = 2 * GateNum  # total number of 2-input gates' inputs
        aNum = (2 * (bitnum + 1) + GateNum - 1) * GateNum + bitnum * bitnum + GateNum * bitnum  # number of variate A
        if not os.path.exists("./oldmc"):
            os.system("mkdir ./oldmc")
        if not os.path.exists("./oldmc/" + Cipherstr):
            os.system("mkdir ./oldmc/" + Cipherstr)
        filestr = "./oldmc/"+Cipherstr + "/oldmc" +str(GateNum) # encoding modle to file
        if not os.path.exists("./"+Cipherstr):
            os.system("mkdir ./"+Cipherstr)
        fout = open(filestr + ".cvc", 'w')
        State_Variate(fout, aNum, bitnum, Size, GateNum, QNum)  # define Variate X, Y A, T, Q
        Trival_Constraint(fout, aNum, bitnum, Size, Sbox)  # Constraints of X, Y A, T, Q
        Logic_Constraint(fout, bitnum, GateNum)  # Encoding of gates' inputs and outputs, S-box outputs
        Objective(fout)
        fout.close()

        order = "stp -p " + str(filestr) + ".cvc "
        start_time = time.time()

        #os.system(order)  # Execute the command to solve
        s=(os.popen(order).read()) #s is solve
        end_time = time.time()
        fouts = open(filestr + ".txt", 'a+')
        fouts.write(str(s))
        fouts.write("searchtime:" + str((end_time - start_time) * 1000))
        fouts.close()
        print("finsh", filestr, float(end_time - start_time) * 1000.0, "ms")

