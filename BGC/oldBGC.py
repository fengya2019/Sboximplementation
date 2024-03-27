import os
import time
import threading
from datetime import datetime
import inspect
import ctypes
A = [[0 for i in range(256)] for j in range(8)]


resstr=""
def Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum):
    countA = 0
    countB = 0
    countQ = 0
    countT = 0
    for k in range(GateNum):
        # Q
        for q in range(2):
            #encoding Q, input of gates
            fout.write("ASSERT(  Q_" +str(countQ)+ " = ")
            for i in range(bitnum):
                x = "A_" + str(countA) + " & X_" + str(i)
                if (k == 0 and i == bitnum - 1):
                    fout.write(x)
                else:
                    fout.write("BVXOR( " + x + ", ")
                countA +=1
            for i in range(countT):
                x = "A_" + str(countA) + " & T_"  + str(i)
                if (i == countT - 1):
                    fout.write(x)
                else:
                    fout.write("BVXOR( " + x + ", ")
                countA+=1
            for i in range(bitnum + countT):
                if (i == bitnum + countT - 1):
                    fout.write(" );\n")
                else:
                    fout.write(" )")
            countQ +=1
        
        #T encoding output of gates
        fout.write("ASSERT( T_" + str(countT) + " = BVXOR( B_" + str(countB) + " & Q_" + str(countQ - 2) + " & Q_" + str(countQ - 1) +
            " , BVXOR( B_" + str(countB + 1) + "& Q_" + str(countQ - 2) + ", BVXOR( B_" + \
            str(countB + 1) + " & Q_" + str(countQ - 1) + ", BVXOR( B_" + str(countB + 2) + " & Q_" + str(countQ - 2)+", B_" + str(countB + 2) +" ) ) ) ) ); \n")
        countB += 3
        countT +=1
    # Y  encoding output of S-box
    for y in range(bitnum):
        fout.write("ASSERT( Y_" + str(y) + " = ")
        for i in range(bitnum):
            x = " A_" + str(countA) + " & X_" + str(i)
            fout.write("BVXOR( "+ x +",")
            countA+=1
        for i in range(GateNum):
            x = " A_" + str(countA) + " & T_" + str(i)
            if (i == GateNum - 1):
                fout.write(x)
            else:
                fout.write("BVXOR( "+ x +",")
            countA+=1
        for i in range(bitnum + countT):
            if (i == bitnum + countT - 1):
                fout.write(" );\n")
            else:
                fout.write(" )")

def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")

if __name__ == '__main__':
    Cipherstr = "PROST"
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST
    BGC = 8  # number of gates
    bitnum = 4
    for GateNum in range(BGC,1,-1):
        Size = pow(2, bitnum) #2^n length
        QNum = 2 * GateNum  #total number of 2-input gates' inputs
        aNum = (2 * bitnum + GateNum - 1) * GateNum  + bitnum * bitnum + GateNum * bitnum #number of variate A
        bNum = 3 * GateNum #number of variate B

        if not os.path.exists("./oldbgc"):
            os.system("mkdir ./oldbgc")
        if not os.path.exists("./oldbgc/" + Cipherstr):
            os.system("mkdir ./oldbgc/" + Cipherstr)

        filestr = "./oldbgc/"+Cipherstr+"/"+Cipherstr+"oldbgc"  #encoding modle to file
        fout=open(filestr + ".cvc", 'w')
        State_Variate(fout, aNum,bitnum, Size, GateNum, QNum, bNum) #define Variate X, Y A, B, T, Q
        Trival_Constraint(fout, aNum,bitnum, Size, GateNum, QNum, bNum, Sbox)#Constraints of X, Y A, B, T, Q
        Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum) #Encoding of gates' inputs and outputs, S-box outputs
        Objective(fout)
        fout.close()

        order="stp -p "+str(filestr)+".cvc "#> "+filestr+".txt " # command: cvc to cnf for cryptominisat

        start_time = time.time()

        #os.system(order)#Execute the command to solve
        s=(os.popen(order)) #s is solve
        end_time = time.time()
        print(s.read())

        s0=(os.popen("rm -f "+filestr+".cvc")) #s is solve
        fouts=open(filestr+str(GateNum)+".txt",'a+')
        fouts.write(str(s.read()))
        fouts.write("searchtime:"+str((end_time - start_time)*1000))
        fouts.close()
        print("finsh",filestr, float(end_time - start_time) * 1000.0,"ms")
