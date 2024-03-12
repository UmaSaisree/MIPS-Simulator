import numpy as np
import sys
import re
file_handle = open('simulation.txt', mode='w')
file_dissembly= open('disassembly.txt', mode='w')

Cycle=0
Reg=np.zeros(32,int)
ImmAddr=[]
instr=[]
Imm=[]

DataAddr=0 
Data=None 
PC=256
InsCat1=['J','JR','BEQ','BLTZ','BGTZ','BREAK','SW','LW','SLL','SRL','SRA','NOP']
InsCat2=['ADD','SUB','MUL','AND','OR','XOR','NOR','SLT','ADDI','ANDI','ORI','XORI']

BreakFlag=False

pre_issue_count=0

waiting_ins = ""
executed_ins = ""

pre_issue_Entry = list()

RegStateUpdate=list()

pre_alu1_Entry = list()


pre_alu2_Entry = list()

pre_mem_ins = ""

post_mem_ins = ""

post_alu2_ins = ""

def printReg():

    file_handle.write("\nRegisters\n")
    for i in range(len(Reg)):
        if i==0:

            file_handle.write("R00:\t{}".format(Reg[i]))
        elif i==8:

            file_handle.write("\nR08:\t{}".format(Reg[i]))
        elif i==16:

            file_handle.write("\nR16:\t{}".format(Reg[i]))
        elif i==24:

            file_handle.write("\nR24:\t{}".format(Reg[i]))
        else:

            file_handle.write("\t{}".format(Reg[i]))

    file_handle.write('\n')
    return
def printData():

    file_handle.write("\nData")
    for i in range(len(Imm)):
        if (ImmAddr[i]-DataAddr)%32==0:

            file_handle.write("\n{}:\t{}".format(ImmAddr[i],Imm[i]))
        else:

            file_handle.write("\t{}".format(Imm[i]))

    file_handle.write('\n')

def com2ori(ori_str):

    if ori_str[0] == '0':
        return ori_str
    if ori_str[0] == '1':
        value_str = ""

        for i in range(len(ori_str)):
            value_str+='1' if ori_str[i] == '0' else '0'

        n = int(value_str, 2) + 1
        com_str = bin(n)[2:]
        if len(com_str) >= len(ori_str):

            com_str = '0' + com_str[1:]
        else:

            n = len(ori_str) - len(com_str) - 1
            for i in range(n):
                com_str = '0' + com_str
            com_str = '1' + com_str
        return com_str

def ori2dec(bin_str):

    if bin_str[0] == '0':
        return int(bin_str, 2)
    if bin_str[0] == '1':
        return -int(bin_str[1:], 2)

def com2dec(com_str):
    ori_str = com2ori(com_str)
    return ori2dec(ori_str)

def dec2ori(dec_num):
    bin_tmp=bin(dec_num)
    if bin_tmp[0] == '-':  
        bin_tmp = '1' + bin_tmp[3:]
    else:  
        bin_tmp = '0' + bin_tmp[2:]
    return bin_tmp

def converTo32bit(bin_str):
    if len(bin_str)<32:
        bin_str=bin_str[0]+(32-len(bin_str))*'0'+bin_str[1:]
    return bin_str

def SRL(dec_num,b):
    if dec_num==-4294967296:
        bin_num="10000000000000000000000000000000"
    else:
        bin_num = bin(dec_num)
        if bin_num[0] == '-':
            bin_num = '1' + bin_num[3:]
        else:
            bin_num = bin_num[2:]
        bin_num = converTo32bit(bin_num)
        bin_num=com2ori(bin_num)
    tmp=b*'0'+bin_num
    bin_num=tmp[0:32]
    return ori2dec(bin_num)

def SLL(dec_num,b):
    bin_num=0
    if dec_num==-4294967296:
        bin_num="10000000000000000000000000000000"
    else:
        bin_num=dec2ori(dec_num)
        bin_num = converTo32bit(bin_num)
        bin_num=com2ori(bin_num)
    tmp=bin_num+b*'0'
    bin_num=tmp[b:]

    return ori2dec(bin_num)


def act_J(instr):
    global PC
    instr_index = instr[6:] 
    instr_index += '00' 
    PC_up4 = bin(0x0F0000000 & PC)
    PC_up4 = PC_up4[2:6]
    if len(PC_up4) < 4:
        cont = 4 - len(PC_up4)
        PC_up4 = cont * '0' + PC_up4
    PC = PC_up4 + instr_index
    PC=int(PC,2)
    disassemble_ins='J'+' '+'#'+str(PC)
    return disassemble_ins

def SRA(dec_num,b):
    if dec_num==-2147483648:
        bin_num="10000000000000000000000000000000"
    else:
        bin_num = bin(dec_num)
        if bin_num[0] == '-':
            bin_num = '1' + bin_num[3:]
        else:
            bin_num = bin_num[2:]
        bin_num = converTo32bit(bin_num)
        bin_num=com2ori(bin_num)
    sign=bin_num[0]
    tmp=b*'0'+bin_num
    bin_num=sign+tmp[1:32]
    return ori2dec(bin_num)

def act_JR(instr):
    global PC
    rs_id=int(instr[6:11],2)
    PC=Reg[rs_id]
    disassemble_ins='JR'+' '+'R'+str(PC)
    return  disassemble_ins

def act_BEQ(instr):
    global PC
    rs_id=int(instr[6:11],2)
    rt_id=int(instr[11:16],2)
    offset = instr[16:32]
    offset+='00'
    offset=int(offset,2)
    if Reg[rs_id]==Reg[rt_id]:
        PC+=offset
    PC+=4
    disassemble_ins='BEQ'+' '+'R'+str(rs_id)+', R'+str(rt_id)+', #'+str(offset)
    return disassemble_ins
def act_BLTZ(instr):
    global PC
    rs_id = int(instr[6:11], 2)
    offset = int(instr[16:32]+"00",2)
    if Reg[rs_id]<0:  
        PC += offset
    PC += 4
    disassemble_ins = 'BLTZ' + ' ' + 'R' + str(rs_id) + ', ' + '#' + str(offset)
    return disassemble_ins

def act_BGTZ(instr):
    global PC
    rs_id = int(instr[6:11], 2)
    offset=int(instr[16:32]+'00',2)
    if Reg[rs_id] > 0:  
        PC += offset
    PC += 4
    disassemble_ins = 'BGTZ' + ' ' + 'R' + str(rs_id) + ', ' + '#' + str(offset)
    return disassemble_ins
def act_BREAK(instr):
    global BreakFlag
    BreakFlag = True
    return "BREAK"
def act_SW(instr):
    base_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    offset = int(instr[16:32], 2)
    memoryAddr=Reg[base_id]+offset
    Imm_id=int((memoryAddr-DataAddr)/4)
    Imm[Imm_id]=Reg[rt_id]
    disassemble_ins = 'SW' + ' ' + 'R' + str(rt_id) + ', ' + str(offset) + '(R' + str(base_id)+')'
    return disassemble_ins
def act_LW(instr):
    base_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    offset = int(instr[16:32], 2)
    memoryAddr = Reg[base_id] + offset
    Imm_id = int((memoryAddr - DataAddr) / 4)
    Reg[rt_id]=Imm[Imm_id]
    disassemble_ins = 'LW' + ' ' + 'R' + str(rt_id) + ', ' + str(offset) + '(R' + str(base_id) + ')'
    return disassemble_ins
def act_SLL(instr):
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    sa = int(instr[21:26], 2)
    tmp=Reg[rt_id]
    Reg[rd_id]=SLL(tmp,sa)
    disassemble_ins = 'SLL' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', '+'#'+str(sa)
    return disassemble_ins
def act_SRL(instr):
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    sa = int(instr[21:26], 2)
    tmp = Reg[rt_id]
    Reg[rd_id] = SRL(tmp, sa)
    disassemble_ins = 'SRL' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', ' + '#' + str(sa)
    return disassemble_ins
def act_SRA(instr):
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    sa = int(instr[21:26], 2)
    tmp = Reg[rt_id]
    Reg[rd_id] = SRA(tmp, sa)
    disassemble_ins = 'SRA' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', ' + '#' + str(sa)
    return disassemble_ins
def act_NOP(instr):
    return 'NOP'

def act_ADD(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    tmp= Reg[rs_id]+Reg[rt_id]
    disassemble_ins='ADD'+' R'+str(rd_id)+', R'+str(rs_id)+', R'+str(rt_id)
    if (tmp>pow(2,31)-1)or(tmp<-pow(2,31)):
        return disassemble_ins
    else:
        Reg[rd_id]=tmp
    return disassemble_ins
def act_SUB(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    tmp = Reg[rs_id] - Reg[rt_id]
    disassemble_ins = 'SUB' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    if (tmp > pow(2, 31) - 1) or(tmp < -pow(2, 31)):
        return disassemble_ins
    else:
        Reg[rd_id] = tmp
    return disassemble_ins
def act_MUL(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    tmp = Reg[rs_id]*Reg[rt_id]
    disassemble_ins = 'MUL' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    if (tmp <= pow(2, 31) - 1) and (tmp >= -pow(2, 31)): 
       Reg[rd_id]=tmp
    else:
        bin_tmp = bin(tmp)
        if bin_tmp[0] == '-':
            bin_tmp = '1' + bin_tmp[3:]
        else:
            bin_tmp = '0'+bin_tmp[2:]
        bin_tmp = com2ori(bin_tmp)
        bin_tmp = bin_tmp[len(bin_tmp) - 32:len(bin_tmp)]
        tmp = com2dec(bin_tmp)
        Reg[rd_id] = tmp
    return disassemble_ins
def act_AND(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id=int(instr[16:21],2)
    Reg[rd_id]=Reg[rs_id]&Reg[rt_id]
    disassemble_ins='AND'+' R'+str(rd_id)+', R'+str(rs_id)+', R'+str(rt_id)
    return disassemble_ins
def act_OR(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    Reg[rd_id] = Reg[rs_id] | Reg[rt_id]
    disassemble_ins = 'OR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    return disassemble_ins
def act_XOR(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    Reg[rd_id] = Reg[rs_id] ^ Reg[rt_id]
    disassemble_ins = 'XOR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    return disassemble_ins
def act_NOR(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    tmp_rs=Reg[rs_id]
    tmp_rt=Reg[rt_id]
    tmp_ans=""
    if tmp_rs==-pow(2,31):
        tmp_rs="10000000000000000000000000000000"
    elif tmp_rt==-pow(2,31):
        tmp_rt="10000000000000000000000000000000"
    else:
        tmp_rs=dec2ori(tmp_rs)
        tmp_rt = dec2ori(tmp_rt)  
        tmp_rs=converTo32bit(tmp_rs)
        tmp_rt = converTo32bit(tmp_rt)  
    for i in range(0,32):
        if not(int(tmp_rs[i])|int(tmp_rt[i])):
            tmp_ans+='1'
        else:
            tmp_ans+='0'
    if tmp_ans=="10000000000000000000000000000000":
        Reg[rd_id] = -pow(2,31)
    else:
        Reg[rd_id]=com2dec(tmp_ans)
    disassemble_ins = 'NOR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    return disassemble_ins
def act_SLT(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    rd_id = int(instr[16:21], 2)
    Reg[rd_id]=1 if Reg[rs_id]<Reg[rt_id] else 0
    disassemble_ins = 'SLT' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
    return disassemble_ins
def act_ADDI(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    tmp_imm = instr[16:32]
    tmp_imm=converTo32bit(tmp_imm)
    tmp_imm=ori2dec(tmp_imm)
    tmp_rt=Reg[rs_id]+tmp_imm
    if tmp_rt>-pow(2,31) and tmp_rt<pow(2,31)-1:
        Reg[rt_id] = tmp_rt
    disassemble_ins = 'ADDI' +  ' R' + str(rt_id) + ', R' + str(rs_id)+ ', #'+str(tmp_imm)
    return disassemble_ins
def act_ANDI(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    tmp_imm = 16*'0'+instr[16:32]
    Reg[rt_id]=Reg[rs_id]&int(tmp_imm,2)
    disassemble_ins = 'ANDI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
    return disassemble_ins
def act_ORI(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    tmp_imm = 16 * '0' + instr[16:32]
    Reg[rt_id] = Reg[rs_id] | int(tmp_imm, 2)
    disassemble_ins = 'ORI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
    return disassemble_ins
def act_XORI(instr):
    rs_id = int(instr[6:11], 2)
    rt_id = int(instr[11:16], 2)
    tmp_imm = 16 * '0' + instr[16:32]
    Reg[rt_id] = Reg[rs_id] ^ int(tmp_imm, 2)
    disassemble_ins = 'XORI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
    return disassemble_ins

class instruction:

    def __init__(self,instr):
        self.insAddr=PC
        self.instr=instr
        self.inType=instr[0:2]
        self.Category = 1 if self.inType == '01' else 2
        self.opBin=instr[2:6]
        self.opDec=int(self.opBin,2)
        self.opName = InsCat1[self.opDec] if self.Category == 1 else InsCat2[self.opDec]
        self.disassemble_ins = ""

        self.rd = None
        self.rs = None
        self.rt = None

        self.ifLWSW=1 if (self.opName=="LW" or self.opName=="SW") else 2
        self.disassemble()

    def display(self):
        print(self.instr,self.insAddr,self.disassemble_ins)
    def getInfo(self):
        return(self.instr+'\t'+str(self.insAddr)+'\t'+self.disassemble_ins+'\n')

    def disassemble_J(self):
        instr_index = self.instr[6:]  
        instr_index += '00'  
        PC_up4 = bin(0x0F0000000 & self.insAddr)
        PC_up4 = PC_up4[2:6]  
        if len(PC_up4) < 4:  
           cont = 4 - len(PC_up4)
           PC_up4 = cont * '0' + PC_up4
        instr_Addr = PC_up4 + instr_index  
        instr_Addr = int(instr_Addr, 2)
        self.disassemble_ins = 'J' + ' ' + '#' + str(instr_Addr)

    def disassemble_JR(self):
        rs_id = int(self.instr[6:11], 2)
        self.disassemble_ins = 'JR' + ' ' + 'R' + str(Reg[rs_id])
        self.rs=rs_id

    def disassemble_BEQ(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        offset = self.instr[16:32]
        offset += '00'
        offset = int(offset, 2)
        self.disassemble_ins = 'BEQ' + ' ' + 'R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(offset)
        self.rs=rs_id
        self.rt=rt_id

    def disassemble_BLTZ(self):
        rs_id = int(self.instr[6:11], 2)
        offset = int(self.instr[16:32] + "00", 2)
        self.disassemble_ins = 'BLTZ' + ' ' + 'R' + str(rs_id) + ', ' + '#' + str(offset)
        self.rs = rs_id

    def disassemble_BGTZ(self):
        rs_id = int(self.instr[6:11], 2)
        offset = int(self.instr[16:32] + '00', 2)
        self.disassemble_ins = 'BGTZ' + ' ' + 'R' + str(rs_id) + ', ' + '#' + str(offset)
        self.rs = rs_id

    def disassemble_BREAK(self):
        self.disassemble_ins ="BREAK"

        return "BREAK"

    def disassemble_SW(self):
        base_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        offset = int(self.instr[16:32], 2)
        self.disassemble_ins = 'SW' + ' ' + 'R' + str(rt_id) + ', ' + str(offset) + '(R' + str(base_id) + ')'
        self.rd = rt_id
        self.rs=base_id

    def disassemble_LW(self):
        base_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        offset = int(self.instr[16:32], 2)
        self.disassemble_ins = 'LW' + ' ' + 'R' + str(rt_id) + ', ' + str(offset) + '(R' + str(base_id) + ')'
        self.rd = rt_id
        self.rs=base_id

    def disassemble_SLL(self):
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        sa = int(self.instr[21:26], 2)
        self.disassemble_ins = 'SLL' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', ' + '#' + str(sa)
        self.rd = rd_id
        self.rt = rt_id

    def disassemble_SRL(self):
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        sa = int(self.instr[21:26], 2)
        self.disassemble_ins = 'SRL' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', ' + '#' + str(sa)
        self.rd = rd_id
        self.rt = rt_id

    def disassemble_SRA(self):
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        sa = int(self.instr[21:26], 2)
        self.disassemble_ins = 'SRA' + ' ' + 'R' + str(rd_id) + ', ' + 'R' + str(rt_id) + ', ' + '#' + str(sa)
        self.rd = rd_id
        self.rt = rt_id

    def disassemble_NOP(self):
        return 'NOP'

    def disassemble_ADD(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'ADD' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_SUB(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'SUB' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_MUL(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'MUL' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_AND(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'AND' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_OR(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'OR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_XOR(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'XOR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_NOR(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'NOR' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_SLT(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        rd_id = int(self.instr[16:21], 2)
        self.disassemble_ins = 'SLT' + ' R' + str(rd_id) + ', R' + str(rs_id) + ', R' + str(rt_id)
        self.rd = rd_id
        self.rt = rt_id
        self.rs = rs_id

    def disassemble_ADDI(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        tmp_imm = self.instr[16:32]
        tmp_imm = converTo32bit(tmp_imm)  
        tmp_imm = ori2dec(tmp_imm)  
        self.disassemble_ins = 'ADDI' + ' R' + str(rt_id) + ', R' + str(rs_id) + ', #' + str(tmp_imm)
        self.rd = rt_id
        self.rs = rs_id

    def disassemble_ANDI(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        tmp_imm = int(16 * '0' + self.instr[16:32], 2)
        self.disassemble_ins = 'ANDI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
        self.rd = rt_id
        self.rs = rs_id

    def disassemble_ORI(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        tmp_imm = int(16 * '0' + self.instr[16:32], 2)
        self.disassemble_ins = 'ORI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
        self.rd = rt_id
        self.rs = rs_id

    def disassemble_XORI(self):
        rs_id = int(self.instr[6:11], 2)
        rt_id = int(self.instr[11:16], 2)
        tmp_imm = int(16 * '0' + self.instr[16:32], 2)
        self.disassemble_ins = 'XORI' + ' R' + str(rs_id) + ', R' + str(rt_id) + ', #' + str(tmp_imm)
        self.rd = rt_id
        self.rs = rs_id

    def disassemble(self):
        if self.Category==1: 
            if self.opName==InsCat1[0]: 
                self.disassemble_J()
            if self.opName==InsCat1[1]: 
                self.disassemble_JR()
            if self.opName==InsCat1[2]:
                self.disassemble_BEQ()
            if self.opName==InsCat1[3]:
                self.disassemble_BLTZ()
            if self.opName == InsCat1[4]:  
                self.disassemble_BGTZ()
            if self.opName == InsCat1[5]:  
                self.disassemble_BREAK()
            if self.opName == InsCat1[6]:  
                self.disassemble_SW()
            if self.opName == InsCat1[7]:  
                self.disassemble_LW()
            if self.opName == InsCat1[8]:  
                self.disassemble_SLL()
            if self.opName == InsCat1[9]:  
                self.disassemble_SRL()
            if self.opName == InsCat1[10]:  
                self.disassemble_SRA()
            if self.opName == InsCat1[11]:  
                self.disassemble_NOP()
        else:
            if self.opName == InsCat2[0]:  
                self.disassemble_ADD()
            if self.opName == InsCat2[1]:  
                self.disassemble_SUB()
            if self.opName == InsCat2[2]:  
                self.disassemble_MUL()
            if self.opName == InsCat2[3]:  
                self.disassemble_AND()
            if self.opName == InsCat2[4]:  
                self.disassemble_OR()
            if self.opName == InsCat2[5]:  
                self.disassemble_XOR()
            if self.opName == InsCat2[6]:  
                self.disassemble_NOR()
            if self.opName == InsCat2[7]:  
                self.disassemble_SLT()
            if self.opName == InsCat2[8]:  
                self.disassemble_ADDI()
            if self.opName == InsCat2[9]:  
                self.disassemble_ANDI()
            if self.opName == InsCat2[10]:  
                self.disassemble_ORI()
            if self.opName == InsCat2[11]:  
                self.disassemble_XORI()

        file_dissembly.write("{}\t{}\t{}\n".format(self.instr,self.insAddr,self.disassemble_ins))

    def actInstr(self):
        if self.Category == 1:  
            if self.opName == InsCat1[0]:  
                self.disassemble_ins = act_J(self.instr)
            elif self.opName == InsCat1[1]:  
                self.disassemble_ins = act_JR(self.instr)
            elif self.opName == InsCat1[2]:  
                self.disassemble_ins = act_BEQ(self.instr)
            elif self.opName == InsCat1[3]:  
                self.disassemble_ins = act_BLTZ(self.instr)
            elif self.opName == InsCat1[4]:  
                self.disassemble_ins = act_BGTZ(self.instr)
            elif self.opName == InsCat1[5]:  
                self.disassemble_ins = act_BREAK(self.instr)
            elif self.opName == InsCat1[6]:  
                self.disassemble_ins = act_SW(self.instr)
            elif self.opName == InsCat1[7]:  
                self.disassemble_ins = act_LW(self.instr)
            elif self.opName == InsCat1[8]:  
                self.disassemble_ins = act_SLL(self.instr)
            elif self.opName == InsCat1[9]:  
                self.disassemble_ins = act_SRL(self.instr)
            elif self.opName == InsCat1[10]:  
                self.disassemble_ins = act_SRA(self.instr)
            elif self.opName == InsCat1[11]:  
                self.disassemble_ins = act_NOP(self.instr)
        else:
            if self.opName == InsCat2[0]:  
                self.disassemble_ins = act_ADD(self.instr)
            elif self.opName == InsCat2[1]:  
                self.disassemble_ins = act_SUB(self.instr)
            elif self.opName == InsCat2[2]:  
                self.disassemble_ins = act_MUL(self.instr)
            elif self.opName == InsCat2[3]:  
                self.disassemble_ins = act_AND(self.instr)
            elif self.opName == InsCat2[4]:  
                self.disassemble_ins = act_OR(self.instr)
            elif self.opName == InsCat2[5]:  
                self.disassemble_ins = act_XOR(self.instr)
            elif self.opName == InsCat2[6]:  
                self.disassemble_ins = act_NOR(self.instr)
            elif self.opName == InsCat2[7]:  
                self.disassemble_ins = act_SLT(self.instr)
            elif self.opName == InsCat2[8]:  
                self.disassemble_ins = act_ADDI(self.instr)
            elif self.opName == InsCat2[9]:  
                self.disassemble_ins = act_ANDI(self.instr)
            elif self.opName == InsCat2[10]:  
                self.disassemble_ins = act_ORI(self.instr)
            elif self.opName == InsCat2[11]:  
                self.disassemble_ins = act_XORI(self.instr)

class InstructionStatus:

    def __init__(self):
        self.table=list()
    def clear(self):
        self.table=[]

    def get_len(self):
        return len(self.table)

    def reset_instruction_status(self):
        ins_len = self.get_len()
        for ins_id in range(ins_len):
            self.table[ins_id]['issue'] = False
            self.table[ins_id]['read_operand'] = False
            self.table[ins_id]['execution'] = False
            self.table[ins_id]['write_result'] = False

    def add_instruction(self, instruction):
        ins_id,op, i, j, k = re.split(' ', instruction)
        instruction = {
            "ins_id":ins_id,
            "op": op,
            "i": i,
            "j": j,
            "k": k,
            "issue": False,
            "read_operand": False,
            "execution": False,
            "write_result": False
            }

        self.table.append(instruction)

class FunctionalUnitStatus:
    def __init__(self):
        self.table =list()
    def printFunc(self):
        for i in range(len(self.table)):
            print(i,self.table[i]["ins_id"])
    def judgeWAR(self, ins_id):
        j=None
        for i in range(len(self.table)):
            if self.table[i]["ins_id"]==ins_id:
                j=i
        for i in range(len(self.table)):
            if not(
                    self.table[i]["Fj"]!=self.table[j]["Fi"]
                    or self.table[i]["Rj"]==False
                    and self.table[i]["Fk"]!=self.table[j]["Fi"]
                    or self.table[i]["Rk"]==False):
                return True
        return False

    def searchFi(self,rd):
        for i in range(len(self.table)):
            if self.table[i]["Fi"]==rd:
                return self.table[i]["ins_id"],self.table[i]["Fi"]
        return None
    def searchFjk(self,rs,rt):
        for i in range(len(self.table)):
            if self.table[i]["Fj"]==rs or self.table[i]["Fk"]==rs or self.table[i]["Fj"]==rt or self.table[i]["Fk"]==rt:
                return True
        return False

class RegisterResultStatus:
    def __init__(self):
        self.register_count = 32

        self.F = [None for i in range(self.register_count)]

    def searchR(self,r):
        if r==None:
            return None
        return self.F[r]

    def issuebookkeeping(self,ins_id,rd):
        if rd:
            self.F[rd]=ins_id

class Scorebord:
    def __init__(self):
        self.insState=InstructionStatus()
        self.func=FunctionalUnitStatus()
        self.reg=RegisterResultStatus()
        self.cycle=0

    def judgeWAW(self,ins: instruction,i:int):
        rd = ins.rd
        if rd==None:
            return False
        if i>0:
            for j in range(i):
                if pre_issue_Entry[j].rd==ins.rd:
                    return True

        if self.reg.searchR(rd):
            return True
        else:
            return False

    def judgeRAW(self,ins: instruction,i:int):

        if i>0:
            for j in range(i):
                if pre_issue_Entry[j].rd==None:
                    continue
                if pre_issue_Entry[j].rd==ins.rs or pre_issue_Entry[j].rd==ins.rt:
                    return True
        fj = ins.rs
        fk = ins.rt
        qj = scoreboard.reg.searchR(fj)
        qk = scoreboard.reg.searchR(fk)
        if qj==ins.insAddr:
            qj=None
        if qk==ins.insAddr:
            qk=None
        rj = not qj
        rk = not qk
        if rj and rk:
            return False
        return True

    def judgeWAR(self,ins: instruction,index:int):
        if ins.rd==None:
            return False
        ins_id=ins.insAddr
        if index>0:

            for j in range(index):
                if pre_issue_Entry[j].rs==ins.rd or pre_issue_Entry[j].rt==ins.rd:
                    return True
        for i in range(len(self.func.table)):
            if i!=ins.insAddr and not (
                    self.func.table[i]["Fj"] != ins.rd
                    or self.func.table[i]["Rj"] == False
                    and self.func.table[i]["Fk"] !=ins.rd
                    or self.func.table[i]["Rk"] == False):

                return True
        return False

    def issuebookkeeping(self,ins: instruction):
        ins_id=ins.insAddr
        busy=True
        op=ins.opName
        fi=ins.rd
        fj=ins.rs
        fk=ins.rt
        qj=self.reg.searchR(fj)
        qk=self.reg.searchR(fk)
        rj=not qj
        rk=not qk
        function_unit = {
            "ins_id": ins_id,
            "ins": ins,
            "Busy": busy,
            "Op": op,
            "Fi": fi,
            "Fj": fj,
            "Fk": fk,
            "Qj": qj,
            "Qk": qk,
            "Rj": rj,
            "Rk": rk
        }
        self.func.table.append(function_unit)
        self.reg.issuebookkeeping(ins_id,fi)
    def deleteFuncState(self,ins_id):
        for i in range(len(self.func.table)):
            if self.func.table[i]["ins_id"]==ins_id:
                self.func.table.remove(self.func.table[i])
                break

    def robookkeeping(self,ins: instruction):
        ins_id=ins.insAddr
        for i in range(len(self.func.table)):
            if self.func.table[i]['ins_id']==ins_id:
                self.func.table[i]["Rj"] = False
                self.func.table[i]["Rk"] = False

    def writebookkeeping(self,ins: instruction):
        ins_id=ins.insAddr
        rd=ins.rd
        for i in range(len(self.func.table)):
            if self.func.table[i]["ins_id"]==ins_id:
                self.func.table[i]["Rj"]=True
            if self.func.table[i]["ins_id"]==ins_id:
                self.func.table[i]["Rk"]=True
        if rd:
            RegStateUpdate.append(rd)

    def RegUpdate(self):
        if len(RegStateUpdate)!=0:
            while(len(RegStateUpdate)!=0):
                self.reg.F[RegStateUpdate[0]] = None
                RegStateUpdate.remove(RegStateUpdate[0])

scoreboard=Scorebord()

def judgeBranchBreakNop(ins: instruction):
    if (ins.opName != 'J' and ins.opName != 'JR' and ins.opName != 'BEQ'
            and ins.opName != 'BLTZ' and ins.opName != 'BGTZ'
            and ins.opName != 'BREAK' and ins.opName != 'NOP'):
        return False
    return True

def ins_fetch():
    global waiting_ins,executed_ins,pre_issue_Entry,PC,BreakFlag,pre_issue_count
    pc_increment=0
    first_ins=None
    second_ins=None
    id_ins = int((PC- 256) / 4)
    if id_ins >= len(instr):
        BreakFlag = True
        return 0
    if executed_ins !="":
        executed_ins = ""
    if waiting_ins != "":  

        fj = waiting_ins.rs
        fk = waiting_ins.rt
        qj = scoreboard.reg.searchR(fj)
        qk = scoreboard.reg.searchR(fk)
        rj = not qj
        rk = not qk

        if   rj and rk:
            executed_ins = waiting_ins
            executed_ins.actInstr()
            waiting_ins=""
        return pc_increment
    if pre_issue_count==4:  
        return 0
    if pre_issue_count<4:
        first_ins=instr[id_ins]
        second_ins =None
        if pre_issue_count<= 2 and id_ins<len(instr)-1:
           second_ins=instr[id_ins+1]
        branch_ins=""
        branch_id=None

        if (judgeBranchBreakNop(first_ins)==False):
            pre_issue_Entry.append(first_ins)
            pc_increment += 4

            if second_ins!=None:
                if(judgeBranchBreakNop(second_ins)==False):
                    pre_issue_Entry.append(second_ins)
                    pc_increment += 4

                else:
                    branch_ins=second_ins
                    branch_id=id_ins+1

        else:
            branch_ins=first_ins
            branch_id = id_ins
        if branch_ins!="":
            fj=instr[branch_id].rs
            fk=instr[branch_id].rt
            qj = scoreboard.reg.searchR(fj)
            qk = scoreboard.reg.searchR(fk)
            rj=not qj
            rk=not qk
            if rj and rk:
                executed_ins = branch_ins
                executed_ins.actInstr()
            else:
                waiting_ins=branch_ins
    pre_issue_count=len(pre_issue_Entry)

    if executed_ins!="":
        pc_increment=0
    #print(pc_increment)
    return pc_increment
def judgeWAWWAR(ins1:instruction,ins2:instruction):
    rd=ins1.rd
    rs=ins2.rs
    rt=ins2.rt
    if(rd!=rs and rd!=rt):
        return
def findInsinFuncState(ins_id):
    for i in range(len(scoreboard.func.table)):
        if scoreboard.func.table[i]["ins_id"]==ins_id:
            return True
    return False
def Issue_unit():
    global pre_issue_count

    if len(pre_issue_Entry) == 0:
        return
    
    
    firstIns=None
    secondIns=None

    for i in range(len(pre_issue_Entry)):
        ins = pre_issue_Entry[i]

        if (not scoreboard.judgeWAW(ins,i)) and (not scoreboard.judgeWAR(ins,i)) and (not findInsinFuncState(ins.insAddr)and(not scoreboard.judgeRAW(ins,i))):
            scoreboard.issuebookkeeping(ins)
            firstIns = ins
            break
        if(findInsinFuncState(ins.insAddr))and(not scoreboard.judgeRAW(ins,i)):
            firstIns = ins
            break

    if firstIns==None:
        return

    if firstIns.ifLWSW==1:

        if len(pre_alu1_Entry)>1:
            return
        pre_alu1_Entry.append(firstIns)
    else:

        if len(pre_alu2_Entry)>1:
            return
        pre_alu2_Entry.append(firstIns)

    pre_issue_Entry.remove(firstIns)

    for i in range(len(pre_issue_Entry)):
        ins = pre_issue_Entry[i]
        if (not scoreboard.judgeWAW(ins,i))and (not scoreboard.judgeWAR(ins,i)) and (not findInsinFuncState(ins.insAddr)):

            if not scoreboard.judgeRAW(ins,i):
                scoreboard.issuebookkeeping(ins)
                secondIns = ins
            break
        if(findInsinFuncState(ins.insAddr))and(not scoreboard.judgeRAW(ins,i)):
            secondIns = ins
            break

    if secondIns==None or firstIns.ifLWSW==secondIns.ifLWSW :
         return

    if secondIns.ifLWSW == 1:  

        if len(pre_alu1_Entry) > 1:
            return
        pre_alu1_Entry.append(secondIns)
    else:

        if len(pre_alu2_Entry) > 1:
            return
        pre_alu2_Entry.append(secondIns)
    pre_issue_Entry.remove(secondIns)
    pre_issue_count=len(pre_issue_Entry)
    return

def ALU():
    global post_alu2_ins,pre_alu1_Entry,pre_mem_ins

    if len(pre_alu1_Entry)!=0:
        ins=pre_alu1_Entry[0]
        scoreboard.robookkeeping(ins)
        pre_mem_ins=ins
        pre_alu1_Entry.remove(ins)

    if len(pre_alu2_Entry) >0:
        ins = pre_alu2_Entry[0]
        scoreboard.robookkeeping(ins)
        post_alu2_ins=ins
        pre_alu2_Entry.remove(ins)
def Mem():
    global pre_mem_ins,post_mem_ins

    if pre_mem_ins != "":
        ins = pre_mem_ins
        post_mem_ins=ins
        if post_mem_ins.opName=="SW":
            post_mem_ins.actInstr()
            scoreboard.writebookkeeping(post_mem_ins)
            scoreboard.deleteFuncState(post_mem_ins.insAddr)
            post_mem_ins=""
        pre_mem_ins=""
def WB():

    global post_alu2_ins,post_mem_ins
    scoreboard.RegUpdate()
    if post_mem_ins!="":
        post_mem_ins.actInstr()
        scoreboard.writebookkeeping(post_mem_ins)
        scoreboard.deleteFuncState(post_mem_ins.insAddr)
        post_mem_ins=""

    if post_alu2_ins!="":
        post_alu2_ins.actInstr()
        scoreboard.writebookkeeping(post_alu2_ins)
        scoreboard.deleteFuncState(post_alu2_ins.insAddr)
        post_alu2_ins=""

with open(sys.argv[1],"r") as f:
    instructions=f.readlines()
ifBreaked=0 
DataAddr=0 

for i in range(0,len(instructions)):
    instructions[i] = instructions[i].strip('\n')
    if ifBreaked!=1:
        if instructions[i][0:6] == '010101':  
            ifBreaked = 1
            DataAddr=PC+4 

        instr_tmp = instruction(instructions[i])
        instr.append(instr_tmp)
    else:
        Imm.append(com2dec(instructions[i]))  
        ImmAddr.append(PC)
        file_dissembly.write("{}\t{}\t{}\n".format(instructions[i],PC,str(com2dec(instructions[i]))))
          

    PC= PC + 4

def printPipeline():
    file_handle.write("--------------------\nCycle {}:\n\n".format(Cycle))
    file_handle.write("IF Unit:\n\tWaiting:")
    if waiting_ins=="":
        file_handle.write("\n")
    else:
        file_handle.write(" [{}]\n".format(waiting_ins.disassemble_ins))
        
    file_handle.write("\tExecuted:")
    if executed_ins=="":
        file_handle.write("\n")
    else:
        file_handle.write(" [{}]\n".format(executed_ins.disassemble_ins))
        
    file_handle.write("Pre-Issue Queue:\n")
    for i in range(4):
        file_handle.write("\tEntry {}:".format(i))
        if i>=len(pre_issue_Entry):
            file_handle.write("\n")
        else:
            file_handle.write(" [{}]\n".format(pre_issue_Entry[i].disassemble_ins))
            
    file_handle.write("Pre-ALU1 Queue:\n")
    for i in range(2):
        file_handle.write("\tEntry {}:".format(i))
        if i>=len(pre_alu1_Entry):
            file_handle.write("\n")
        else:
            file_handle.write(" [{}]\n".format(pre_alu1_Entry[i].disassemble_ins))
            
    file_handle.write("Pre-MEM Queue:")
    if pre_mem_ins=="":
        file_handle.write("\n")
    else:
        file_handle.write(" [{}]\n".format(pre_mem_ins.disassemble_ins))
    file_handle.write("Post-MEM Queue:")
    if post_mem_ins=="":
        file_handle.write("\n")
    else:
        file_handle.write(" [{}]\n".format(post_mem_ins.disassemble_ins))
        
    file_handle.write("Pre-ALU2 Queue:\n")
    for i in range(2):
        file_handle.write("\tEntry {}:".format(i))
        if i>=len(pre_alu2_Entry):
            file_handle.write("\n")
        else:
            file_handle.write(" [{}]\n".format(pre_alu2_Entry[i].disassemble_ins))
            
    file_handle.write("Post-ALU2 Queue:")
    if post_alu2_ins=="":
        file_handle.write("\n")
    else:
        
        file_handle.write(" [{}]\n".format(post_alu2_ins.disassemble_ins))

PC=256

id_ins=int((PC-256)/4)

while(not BreakFlag):
    Cycle = Cycle + 1
    WB()
    Mem()
    ALU()
    Issue_unit()
    PC=ins_fetch()+PC
    printPipeline()
    printReg()
    printData()
    pre_issue_count=len(pre_issue_Entry)
file_dissembly.close()
file_handle.close()