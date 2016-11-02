#! python
# (c) DL, UTA, 2009 - 2011
import  sys, string, time
wordsize = 24                                        # everything is a word
numregbits = 3                                       # actually +1, msb is indirect bit
opcodesize = 5
addrsize = wordsize - (opcodesize+numregbits+1)      # num bits in address
memloadsize = 1024                                   # change this for larger programs
numregs = 2**numregbits
regmask = (numregs*2)-1                              # including indirect bit
addmask = (2**(wordsize - addrsize)) -1
nummask = (2**(wordsize))-1
opcposition = wordsize - (opcodesize + 1)            # shift value to position opcode
reg1position = opcposition - (numregbits +1)            # first register position
reg2position = reg1position - (numregbits +1)
memaddrimmedposition = reg2position                  # mem address or immediate same place as reg2
realmemsize = memloadsize * 1                        # this is memory size, should be (much) bigger than a program
#memory management regs
codeseg = numregs - 1                                # last reg is a code segment pointer
dataseg = numregs - 2                                # next to last reg is a data segment pointer
#ints and traps
memval = 0
score= []
trapreglink = numregs - 3                            # store return value here
trapval     = numregs - 4                            # pass which trap/int
mem = [0] * realmemsize                              # this is memory, init to 0
reg = [0] * numregs                                  # registers
clock = 0                                            # clock starts ticking
ic = 0
taken = 0
val = 0                                          # instruction count
numcoderefs = 0                                      # number of times instructions read
numdatarefs = 0                                      # number of times data read
starttime = time.time()
curtime = starttime
ifetch_decode_flag = 1
ofetch_execute_flag = 0
cache_hits=0
cache_miss=0
wback_flag = 0
bnz_flg=0
ip = 0
DataHazards=0
addre=0
branch_hazard =0
stagecounter = 0
numDataHits=0
numDataMiss=0
numInstHits=0
numInstMiss=0
#If cache is of Unified,double word,direct,4lines = 4x3 array . first column stores TAG
unified_cache=[[None,None,None],[None,None,None],[None,None,None],[None,None,None]]

#If cache is of Split,quad word,4 way (4 set 4 blocks each),16 lines = 16x5 arrays
split_cache = [[None for col in range(4)] for row in range(16)]

def scoreboard(opcode, reg1):
   opc = opcode
   r = reg1
   global score
   if opc in [1,2,3,4,7,9]:
       score.append(['W',r])
       op = 'W'
   if opc in [8,13,14,16]:
       score.append(['R',r])
       op = 'R'
   if opc in [12]:
       score.append(['Branch',r])
       op = 'Branch'
   return op,r


#give as to which cache to use
arguments=sys.argv
if len(arguments) != 2:
    print 'invalid syntax , needs two arguments'
    print('Usage: %s [cache unified/split]' % arguments[0])
    sys.exit(2)

cache_flg=''
cache_flg = arguments[1]
if not cache_flg == 'unified' and not cache_flg == 'split':
    print('%s is not a valid input input,unified or split' % cache_flg)
    sys.exit(2)

if cache_flg == 'unified':
    print 'In use : Unified,double word,direct,4lines cache'
else:
    print 'In use :  Split,quad word,4 way,16 lines'

def caching(types,addres):
    global cache_hits
    global cache_miss
    global cache_flg
    global numDataHits
    global numDataMiss
    global numInstHits
    global numInstMiss

    if cache_flg=='unified':
        #using ip and converting it to bits
        bin_addr = bin(addres)[2:].zfill(10)
        TAG=bin_addr[0:7] # tag
        last_3=bin_addr[7:]
        sec_last=last_3[:2]
        last_bit=bin_addr[9:]

        #bits to array indices
        cache_col=int(last_bit,2)
        cache_row=int(sec_last,2) #block
        my_cache_col = cache_col+1 #offset

        print ('checking cache for addres:%s[%s] in array[block:%s][offset:%s] with TAG:%s' %(addres,bin_addr,cache_row,my_cache_col,TAG))

        if unified_cache[cache_row][0] == TAG:
            if unified_cache[cache_row][my_cache_col] != None:
                cache_hits=cache_hits+1
                present=unified_cache[cache_row][my_cache_col]
                print ('HIT. array[%s][%s]: with tag:%s,has value:%s' %(cache_row,my_cache_col,TAG,present))
                print 'Total cache hits:',cache_hits
                return present
            else:
                mem_val=mem[addres]#mem access
                unified_cache[cache_row][my_cache_col]=mem_val
                cache_miss=cache_miss+1
                print ('MISS. array[%s][%s]: with tag %s has no value, putting in new value: %s' %(cache_row,my_cache_col,TAG,mem_val))
                print 'Total cache miss:',cache_miss
                return mem_val
        else: #not in cache so insert
            mem_val=mem[addres]
            if unified_cache[cache_row][0] == None: #if TAG is none
                unified_cache[cache_row][0] = TAG
                unified_cache[cache_row][my_cache_col] = mem_val
                cache_miss=cache_miss+1
                print ('Cache Miss. array[%s][%s]: with tag None.Saving new tag/value: %s/%s' %(cache_row,my_cache_col,TAG,mem_val))
                print 'Total cache miss:',cache_miss
                return mem_val
            else: #replace
                old_TAG=unified_cache[cache_row][0]
                old_val=unified_cache[cache_row][my_cache_col]
                unified_cache[cache_row][0] = TAG
                unified_cache[cache_row][1]=None #clear cache
                unified_cache[cache_row][2]=None
                unified_cache[cache_row][my_cache_col] = mem_val #only store the value got
                cache_miss=cache_miss+1
                print ('Miss. Replace array[%s][%s] with old value:%s/%s with a newer value:%s/%s' %(cache_row,my_cache_col,old_TAG,old_val,TAG,mem_val))
                print 'Total cache miss:',cache_miss
                return mem_val
    elif cache_flg == 'split':
        bin_addr = bin(addres)[2:].zfill(10)
        last_6=bin_addr[4:]
        first_4=last_6[:4]
        first_2=first_4[:2]
        sec_2_bits=first_4[2:]
        third_2_bits=last_6[4:]

        #convert bits to integer as array indices
        set_order=int(first_2,2)
        block_addr=int(sec_2_bits,2)
        block_offst=int(third_2_bits,2)

        print ('checking %s cache for address:%s[%s] set:%s block:%s offset:%s' %(types,addres,bin_addr,set_order,block_addr,block_offst))
        print split_cache

        if types=='inst':
            cache_row=set_order+block_addr
            cache_col=block_offst
            print split_cache[set_order][cache_col]
            if split_cache[set_order][cache_col] != None:
                cache_val=split_cache[set_order][cache_col]
                cache_hits=cache_hits+1
                numInstHits=numInstHits+1
                print ('instruction Cache Hit. set:%s block:%s offset:%s value:%s' %(set_order,block_addr,block_offst,cache_val))
                print 'Total cache hits:',cache_hits
                print 'total inst hits:',numInstHits
                return cache_val
            else: #not in cache so insert or replace, but max 32 words(8x4)
                active_val=mem[addres]
                if split_cache[cache_row][cache_col] == None:
                    split_cache[cache_row][cache_col] = active_val
                    cache_miss=cache_miss+1
                    numInstMiss=numInstMiss+1
                    print ('Instruction Cache Miss. set:%s block:%s offset:%s value is None,saving value:%s' %(set_order,block_addr,block_offst,active_val))
                    print 'Total cache miss:',cache_miss
                    print 'total inst miss:', numInstMiss
                    return active_val
                else: #replacement time
                    old_val=split_cache[cache_row][cache_col]
                    split_cache[cache_row][cache_col] = active_val
                    cache_miss=cache_miss+1
                    numInstMiss=numInstMiss+1
                    print ('instruction Cache Miss.Replace set:%s block:%s offset:%s old value:%s with new value:%s' %(set_order,block_addr,block_offst,old_val,active_val))
                    print 'Total cache miss:',cache_miss
                    print 'total inst miss:', numInstMiss

                    return active_val
        elif types=='data':
            global numDataHits
            cache_row=set_order+block_addr+7
            cache_col=block_offst
            if split_cache[cache_row][cache_col] != None:
                cache_val=split_cache[set_order][cache_col]
                cache_hits=cache_hits+1
                numdataHits=numDataHits+1
                print ('Data Cache Hit. set:%s block:%s offset:%s value:%s' %(set_order,block_addr,block_offst,cache_val))
                print 'Total cache hits:',cache_hits
                print 'total data hits:',numDataHits
                return cache_val
            else: #not in cache so insert or replace, but max 32 words(8x4)
                active_val=mem[addres]
                if split_cache[cache_row][cache_col] == None:
                    split_cache[cache_row][cache_col] = active_val
                    cache_miss=cache_miss+1
                    numDataMiss=numDataMiss+1
                    print ('Data Cache Miss. set:%s block:%s offset:%s value is None,saving value:%s' %(set_order,block_addr,block_offst,active_val))
                    print 'Total cache miss:',cache_miss
                    print 'total data miss:',numDataMiss
                    return active_val
                else:
                    old_val=split_cache[cache_row][cache_col]
                    split_cache[cache_row][cache_col] = active_val
                    cache_miss=cache_miss+1
                    numDataMiss=numDataMiss+1
                    print ('Data Cache Miss.Replace set:%s block:%s offset:%s old value:%s with new value:%s' %(set_order,block_addr,block_offst,old_val,active_val))
                    print 'Total cache miss:',cache_miss
                    print 'total data miss:',numDataMiss
                    return active_val
        else:
            print 'select right cache type'
    else:
        print 'select right cache type '

def startexechere ( p ):
    # start execution at this address

    reg[ codeseg ] = p
def loadmem():                                       # get binary load image
  curaddr = 0
  for line in open("a.out", 'r').readlines():
    token = string.split( string.lower( line ))      # first token on each line is mem word, ignore rest
    if ( token[ 0 ] == 'go' ):
        startexechere(  int( token[ 1 ] ) )
    else:
        mem[ curaddr ] = int( token[ 0 ], 0 )
        curaddr = curaddr = curaddr + 1
def getcodemem ( a ):

    # get code memory at this address
    addres =  a + reg[ codeseg ]                   # fetch will call this function, counter for instruction fetch

    cache_val=caching('inst',addres)
    memval = mem[ a + reg[ codeseg ] ]
    return(cache_val)
def getdatamem ( a):
    # get code memory at this address
    addres = a + reg[ dataseg ]
    cache_val=caching('data',addres)
    memval = mem[ a + reg[ dataseg ] ]
    return ( cache_val)
    #return(memval)

def setdatamem (regcontents, memaddr):
    mem[memaddr + reg[dataseg]] = regcontents
    return (mem[memaddr + reg[dataseg]])

def getregval ( r ):
    # get reg or indirect value
    if ( (r & (1<<numregbits)) == 0 ):               # not indirect
       rval = reg[ r ]
    else:
       global numdatarefs
       rval = getdatamem( reg[ r - numregs ] )       # indirect data with mem address
       numdatarefs = numdatarefs + 1
    return ( rval )
def checkres( v1, v2, res):
    v1sign = ( v1 >> (wordsize - 1) ) & 1
    v2sign = ( v2 >> (wordsize - 1) ) & 1
    ressign = ( res >> (wordsize - 1) ) & 1
    if ( ( v1sign ) & ( v2sign ) & ( not ressign ) ):
      return ( 1 )
    elif ( ( not v1sign ) & ( not v2sign ) & ( ressign ) ):
      return ( 1 )
    else:
      return( 0 )
def dumpstate ( d ):
    if ( d == 1 ):
        print reg
    elif ( d == 2 ):
        print mem
    elif ( d == 3 ):
        global DataHazards
        global branch_hazard
        global taken
        CPI = clock / ic
        current_time = time.time()
        runtime = current_time-starttime
        IPS = ic / runtime      # changes as per comments
        MIPS = IPS / 10**6      # MIPS calculation
        Memory_Reference = numcoderefs+numdatarefs
        opc,r = scoreboard(opcode,reg1)
        print '\n',score,'\n'
        print 'clock=', clock, 'IC=', ic, 'Coderefs=', numcoderefs,'Datarefs=', numdatarefs, 'Start Time=', starttime, 'Currently=', time.time()
        print 'CPI=', CPI
        print 'IPS=', IPS
        print 'MIPS=', MIPS
        print 'Memory_Reference=', Memory_Reference
        total = DataHazards + branch_hazard
        print 'Num Data Hazard=', DataHazards
        Num_Data_Hazard = branch_hazard/2
        print 'Num Branch Hazard=',Num_Data_Hazard #stall 2 cycles for every brach
        print 'Total Stalls=',total
        print 'no of branches predicted properly:',taken
        tken_prcnt1 = taken/(0.01*Num_Data_Hazard)
        taken_percent = tken_prcnt1*100
        print 'taken percentage:',float(tken_prcnt1)

def trap ( t ):
    # unusual cases
    # trap 0 illegal instruction
    # trap 1 arithmetic overflow
    # trap 2 sys call
    # trap 3+ user
    rl = trapreglink                            # store return value here
    rv = trapval
    if ( ( t == 0 ) | ( t == 1 ) ):
       dumpstate( 1 )
       dumpstate( 2 )
       dumpstate( 3 )
    elif ( t == 2 ):                          # sys call, reg trapval has a parameter
       what = reg[ trapval ]
       if ( what == 1 ):
           a = a        #elapsed time
    return ( -1, -1 )
    return ( rv, rl )

def Stage1(ip,ic):
   global numcoderefs
   ir = getcodemem( ip )                            # - fetch
   ip = ip + 1
   numcoderefs = numcoderefs + 1
   opcode = ir >> opcposition                       # - decode
   reg1   = (ir >> reg1position) & regmask
   reg2   = (ir >> reg2position) & regmask
   addr   = (ir) & addmask
   ic = ic + 1

   return ip, ic, opcode, reg1, reg2, addr

def Stage2(opcode, reg1, reg2, addr, ip, ic):
   operand2 = 0
   result = 0
   bnz_flag = 0
   tval = 0
   treg = 0
   opcode_null = 0
   no_operands = 0
   global clock
   global numdatarefs
   if not (opcodes.has_key( opcode )):              # - operand fetch
      tval, treg = trap(0)

      if (tval == -1):                              # illegal instruction
         print 'hit an illegal instruction'
         #break

   memdata = 0                                     # contents of memory for loads

   if opcodes[ opcode ] [0] == 1:                   # dec, inc, ret type
      operand1 = getregval( reg1 )                  # fetch operands
      no_operands = 1
   elif opcodes[ opcode ] [0] == 2:                 # add, sub, and type
      operand1 = getregval( reg1 )                  #fetch operands
      operand2 = getregval( reg2 )
      no_operands = 2
   elif opcodes[ opcode ] [0] == 3:                 #ld, st, br, shiftr, shiftl type
      operand1 = getregval( reg1 )                  #fetch operands
      operand2 = addr
      no_operands = 3
   elif opcodes[ opcode ] [0] == 0:                 #NULL POINTER TYPE
      print 'no of operand 0 cant work'
      no_operands = 0
      #break, couldnt use it to brak from if

   if (opcode == 7):                                #get data memory for loads
      memdata = getdatamem( operand2 )

   # - execute

   if opcode == 1:                                  #add
      result = (operand1 + operand2) & nummask

      if ( checkres( operand1, operand2, result )):
         tval, treg = trap(1)

         if (tval == -1):                          #overflow
            print 'arithmetic overflow'
            #break

   elif opcode == 2:                                #sub
      result = (operand1 - operand2) & nummask
      if ( checkres( operand1, operand2, result )):
         tval, treg = trap(1)
         if (tval == -1):                           #overflow
            print 'overflow on subtract'
            #break

   elif opcode == 3:                                #dec
      result = operand1 - 1

   elif opcode == 4:                                #inc
      result = operand1 + 1

   elif opcode == 5:                                #and
      result = (operand1 & operand2) & nummask


   elif opcode == 7:                                #load
     #global numdatarefs
     result = memdata
     numdatarefs = numdatarefs + 1

   elif opcode == 8:                                #store
     #global numdatarefs
     result = operand1
     numdatarefs = numdatarefs + 1

   elif opcode == 9:                                #load immediate
     result = operand2

   elif opcode == 12:                               #conditional branch
     result = operand1
     bnz_flag = opcode
     if result <> 0:       #cannot include branch prediction here cause we cannot make value 0 if brnch not taken
        ip = operand2


   elif opcode == 13:                               #branch and link
     result = ip
     ip = operand2

   elif opcode == 14:                               #return
     ip = operand1

   elif opcode == 16:                               #interrupt/sys call
     result = ip
     clock = clock +2;
     tval, treg = trap(1)
     if (tval == -1):
      print 'interrupt!!!'
      #break
     reg1 = treg
     ip = operand2


   return result, operand1, operand2, memdata, ip, bnz_flag, tval, no_operands



#writeback
def Stage3(opcode, result, ip, ic):

   ip, ic, opcode, reg1, reg2, addr = Stage1(ip-2, ic-2)

   if ( (opcode == 1) | (opcode == 2 ) | (opcode == 3) | (opcode == 4 ) | (opcode == 5 )):     # arithmetic, and
        reg[ reg1 ] = result
   elif ( (opcode == 7) | (opcode == 9 )):     # loads, shiftl, shiftr
        reg[ reg1 ] = result
   elif (opcode == 13):                        # store return address
        reg[ reg1 ] = result
   elif (opcode == 16):                        # store return address
        reg[ reg1 ] = result
   elif (opcode == 8):                                #store
        #result = setdatamem(result, addr)
        mem[operand2 + reg[dataseg]] = result

   print '|WB |',opcodes[ opcode ] [1]
   print 'Trace=', 'Instruction Pointer=',ip, "Reg1=", getregval(reg1), "Reg2=", getregval(reg2), "Opcode=", opcode, "Memory_Address=", addr


   return

startexechere( 0 )                                  # start execution here if no "go"
loadmem()                                           # load binary executable



# opcode type (1 reg, 2 reg, reg+addr, immed), mnemonic
opcodes = { 1: (2, 'add'), 2: ( 2, 'sub'),
            3: (1, 'dec'), 4: ( 1, 'inc' ),
            7: (3, 'ld'),  8: (3, 'st'), 9: (3, 'ldi'),
           12: (3, 'bnz'), 13: (3, 'brl'),
           14: (1, 'ret'),
           16: (3, 'int') }
# while instruction is not halt
print "Stage1-Stage2-Stage3"
while( 1 ):
   stagecounter = stagecounter+1
   print '\n In stage', stagecounter, '\n'



   if (ic == 1):
      #opc, r = scoreboard(opcode, reg1)
      #scoreboard.append([opc,r])
      #print opc
      #print r
      ifetch_decode_flag = 1
      ofetch_execute_flag = 1
      wback_flag = 0
      clock = clock + 1;

   elif (ic == 2):
      #opc, r = scoreboard(opcode, reg1)
      #scoreboard.append([opc,r])
      ifetch_decode_flag = 1
      ofetch_execute_flag = 1
      wback_flag = 1
      clock = clock + 1 ;

   elif (ic >= 3):
      #opc, r = scoreboard(opcode, reg1)
      #scoreboard.append([opc,r])
      ifetch_decode_flag = 1
      ofetch_execute_flag = 1
      if bnz_flag != 12:
         wback_flag = 1
      else:
         wback_flag = 0
         #print 'ip is', ip
      clock = clock + 1;

   if (wback_flag == 1):


      Stage3 (opcode, result, ip, ic)



   if (ofetch_execute_flag == 1):

      result, operand1, operand2, memdata, ip, bnz_flag, tval, no_operands = Stage2(opcode, reg1, reg2, addr, ip, ic)


      if (tval == -1):                              # illegal instruction, overflow, interrupt/sys call
         stagecounter = stagecounter + 1;
         print 'In stage:', stagecounter
         break;
      if (no_operands == 0):
         break
      if bnz_flag == 12:
          #global ip
          #branch_predict = []
          #b = branch_predict[ip]
          branch_predict = {}
          b = branch_predict.get(ip,False)


          if operand1 !=0:
            global taken
            print 'content is', operand1, 'not zero'
            print 'jump to address', reg[codeseg]+operand2
            print 'branch taken'
            branch_predict[ip] = 1
            taken = taken + 1
          else:

            print '|OF & EX |',opcodes[ opcode ] [1]
            #print '|',stagecounter, '|', opcodes[ opcode ] [1]
            print 'branch not taken stall till write back'
            branch_predict[ip] = 0
            clock = clock + 2
            #total = total + 2 #increase the stall

      else:

         if no_operands == 1:
             global DataHazards
             print '|OF & EX |',opcodes[ opcode ] [1]
             opr,r = scoreboard(opcode,reg1)
             previous = score[ip-1]
             if (((opr =="R" and previous[0] == "W")  or (opr =="W" and previous[0] == "R")) and previous[1]== reg1):
                 print ' HAZARD ! Stall 1 Cycle'
                 ofetch_execute_flag = 0
                 DataHazards = DataHazards+1
                 clock = clock + 1

             if ((previous[1]==reg1) or (previous[1]==reg2)):
                print 'same register, stall'
                DataHazards = DataHazards+1
                clock = clock +1
            #print '|', stagecounter,'|', opcodes[ opcode ] [1]
         elif no_operands == 2:
             print '|OF & EX |',opcodes[ opcode ] [1]
             global DataHazards
             opr,r = scoreboard(opcode,reg1)
             previous = score[ip-1]
             if (((opr =="R" and previous[0] == "W")  or (opr =="W" and previous[0] == "R")) and previous[1]== reg1):
                 print ' HAZARD ! Stall 1 Cycle'
                 ofetch_execute_flag = 0
                 DataHazards = DataHazards+1
                 clock = clock + 1

             if ((previous[1]==reg1) or (previous[1]==reg2)):
                print 'same register, stall'
                DataHazards = DataHazards+1
                clock = clock +1
            #print '|', stagecounter,'|', opcodes[ opcode ] [1]
            #print '|', stagecounter,'|', operand2
         elif no_operands == 3:
             global DataHazards
             print '|OF & EX |',opcodes[ opcode ] [1]
             opr,r = scoreboard(opcode,reg1)
             previous = score[ip-1]
             if (((opr =="R" and previous[0] == "W")  or (opr =="W" and previous[0] == "R")) and previous[1]== reg1):
                 print ' HAZARD ! Stall 1 Cycle'
                 ofetch_execute_flag = 0
                 DataHazards = DataHazards+1
                 clock = clock +1

             if ((previous[1]==reg1) or (previous[1]==reg2)):
                print 'same register, stall'
                DataHazards = DataHazards+1
                clock = clock +1
            #print '|', stagecounter,'|', opcodes[ opcode ] [1]
            #print '|',stagecounter, '|', operand2


   if (ifetch_decode_flag == 1):

      ip, ic, opcode, reg1, reg2, addr = Stage1(ip,ic)
      print '|IF & ID |',opcodes[ opcode ] [1]

      #print '|',stagecounter,'|', opcodes[ opcode ] [1]
      clock = clock + 1
      opr,r = scoreboard(opcode,reg1)
      previous = score[ip-1]
      #print 'ip:', ip
      #print 'board of ip-1:', score[ip-1]
      #previous=score[ip-1]
      #previous is the operation array of previous ip, and we compare with current operation opr
      print score
      #or ( opr=="W" and previous[0] == "W")
      if (((opr =="R" and previous[0] == "W")  or (opr =="W" and previous[0] == "R")) and previous[1]== reg1):
          print ' HAZARD ! Stall 1 Cycle'
          ofetch_execute_flag = 0
          DataHazards = DataHazards+1
          #print 'hazards count =', DataHazards
          clock = clock+1
      if ((previous[1]==reg1) or (previous[1]==reg2)):
         print 'same register, stall'
         DataHazards = DataHazards+1
         clock = clock +1

      if(opr=="Branch"):
         print 'Branch Hazard ! stall till next writeback stage finish'
         ofetch_execute_flag = 1
         ifetch_decode_flag = 0 # donot fetch next intruction till the address is knwn
         branch_hazard = branch_hazard + 2
         clock = clock + 2

   # end of instruction loop
# end of execution
