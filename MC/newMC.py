import os
import time
import threading
from datetime import datetime
import inspect
import ctypes

result = 0

A = [[0 for i in range(256)] for j in range(8)]
resstr = ""
resultstr = ""
def Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, depth, SS):
    countA = 0
    countB = 0
    countQ = 0
    countT = 0
    countX = 0
    countY = 0
    lenght = bitnum
    # print(SS)
    # print(depth)
    for d in range(depth):
        # print(d,countT)
        Logic_SubConstraint(fout, bitnum, Size, SS[d], countQ, countT, d, lenght)
        countQ = countQ + 2 * SS[d]
        countT = countT + SS[d]
        lenght = lenght + SS[d]
        # print(lenght)
        # Y
    for y in range(1):
        fout.write("ASSERT(  Y_" + str(y) + " = ")
        for i in range(bitnum):
            x = "( IF A_" + str(countQ) + "[" + str(bitnum + countT - 1 - i) + ":" + str(
                bitnum + countT - 1 - i) + "]=0bin0 THEN 0bin"
            xx = ""
            for j in range(Size):
                xx = xx + str(0)
            x = x + xx + " ELSE  X_" + str(i) + " ENDIF )"
            fout.write("BVXOR( " + x + ", ")
        for i in range(GateNum):
            x = "( IF A_" + str(countQ) + "[" + str(countT - 1 - i) + ":" + str(countT - 1 - i) + "]=0bin0 THEN  0bin"
            xx = ""
            for j in range(Size):
                xx = xx + str(0)
            x = x + xx + " ELSE T_" + str(i) + " ENDIF )"
            if (i == GateNum - 1):
                fout.write(x)
            else:
                fout.write("BVXOR( " + x + ", ")
        for i in range(bitnum + countT):
            if (i == bitnum + countT - 1):
                fout.write(" );\n")
            else:
                fout.write(" )")
        countQ += 1


def Objective(fout):
    fout.write("QUERY(FALSE);\nCOUNTEREXAMPLE;\n")


def _async_raise(tid, exctype):
    tid = ctypes.c_long(tid)
    if not inspect.isclass(exctype):
        exctype = type(exctype)
    res = ctypes.pythonapi.PyThreadState_SetAsyncExc(tid, ctypes.py_object(exctype))
    if res == 0:
        raise ValueError("invalid thread id")
    elif res != 1:
        ctypes.pythonapi.PyThreadState_SetAsyncExc(tid, None)
        raise SystemError("PyThreadState_SetAsyncExc failed")


def stop_thread(thread):
    _async_raise(thread.ident, SystemExit)


def time_stamp1():
    ct = time.time()
    local_time = time.localtime(ct)
    data_head = time.strftime("%Y%m%d%H%M%S", local_time)
    data_secs = (ct - int(ct)) * 1000
    time_stamp = "%s%03d" % (data_head, data_secs)
    return time_stamp

if __name__ == '__main__':
    Cipherstr = "PROST"  # ciphername
    Sbox = [0, 4, 8, 15, 1, 5, 14, 9, 2, 7, 10, 12, 11, 13, 6, 3]  # PROST# S-box
    MC = 8  # number of AND gates
    bitnum = 4  # number of S-box inputs
    for GateNum in range(MC, 1, -1):
        Size = pow(2, bitnum)
        QNum = 2 * GateNum
        bNum = GateNum
        l = []
        for j in range(1, GateNum + 1):
            l.append(j)
        for depth in range(1, GateNum + 1):
            SStr = []
            combination_impl(l, GateNum, [], depth, SStr)
            SStr0 = []
            for dd in range(len(SStr)):
                SS = SStr[len(SStr) - dd - 1]
                ff = 1
                gs = 1
                g0 = 0
                for sd in range(len(SS)):
                    if SS[len(SS) - sd - 1] > gs + g0:
                        ff = 0
                        break
                    g0 = g0 + gs - SS[len(SS) - sd - 1]
                    gs = 2 * SS[len(SS) - sd - 1]
                if (ff):
                    SStr0.append(SS)
            x = 1
            val = 1
            issolver = 0
            # print(SStr0)
            for d in range(len(SStr0)):
                result = 0
                SS = SStr0[d]
                print(SS)
                if not os.path.exists("./mc"):
                    os.system("mkdir ./mc")
                if not os.path.exists("./mc/"+Cipherstr):
                    os.system("mkdir ./mc/"+Cipherstr)
                filestr = "./mc/" + Cipherstr + "/" + Cipherstr + "newmc_D" + str(depth)
                fout = open(filestr + "0.cvc", 'w')
                State_Variate(fout, bitnum, Size, GateNum, QNum, bNum, SS)
                Trival_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, Sbox)
                Logic_Constraint(fout, bitnum, Size, GateNum, QNum, bNum, depth, SS)
                Objective(fout)
                fout.close()
                fout0 = open(filestr + "1.cvc", 'w')
                fout1 = open(filestr + "2.cvc", 'w')
                # fout2=open(filestr + ".txt", 'w')
                b0str = ""
                b1str = ""
                for j in range(0, QNum, 2):
                    b0str = b0str + "ASSERT( BVGT(A_" + str(j) + ", A_" + str(j + 1) + "));\n"
                    b1str = b1str + "ASSERT( BVGT(A_" + str(j + 1) + ", A_" + str(j) + "));\n"
                lines0 = []
                lines = []
                f = open(filestr + "0.cvc", 'r')
                s = ""
                s0 = ""
                for line in f:
                    lines.append(line)
                    lines0.append(line)
                lines0.insert(4 + 2 * bitnum + GateNum, b0str)
                lines.insert(4 + 2 * bitnum + GateNum, b1str)
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
                    p = threading.Thread(target=thread_func, args=(threads, str(filestr) + str(j),))
                    threads.append(p)
                # print(threads)
                # p.start()
                resultstr = ""
                result = 0
                ishassolver = 0
                for t in threads:
                    t.start()
                x = 1
                # print(result)
                while (x):
                    # print(result)
                    xx = 0
                    # end_time = time.time()
                    # if end_time - start_time > 600:
                    #    xx = 1
                    if result == 1:  # len(cipher):
                        x = 0
                        for line in resultstr.splitlines():
                            s = line.split()
                            if "Invalid." in s:
                                # print(resultstr)

                                # MinGEC=MinGEC-1
                                ishassolver = 1
                                result = 1
                                break
                            if "Valid." in s:
                                # print(resultstr)

                                # MinGEC=MinGEC-1
                                ishassolver = 0
                                result = 0
                                resultstr = ""
                                break
                        # print(depth,resultstr)
                        order = "ps -ef|grep " + filestr
                        # os.system(order)
                        res = os.popen(order).read()
                        for line in res.splitlines():
                            s = line.split()
                            if filestr + "0.cvc" in s or filestr + "1.cvc" in s or filestr + "2.cvc" in s:
                                # print(s[1])
                                r = os.popen("kill -9 " + s[1]).read()
                                # print("---------------------")
                                # os.system(order)

                        print(os.system("rm -f " + filestr + "*.cvc"))
                        print("rm -f " + filestr + "*.cvc")
                    if ishassolver:
                        print(depth)
                        break


