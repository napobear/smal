program smal6502(input,output,obj,inp1,inp2,inp3);
      { Simple macro assembler and linkage editor with a 16 bit
	 word. started by D. W. Jones in the fall 1980 at the
	 university of iowa. rev 4/20/82 includes complete macro and
	 conditional support, implemented on prime hull v-mode pascal.
	 rev 5/7/82 to support 6502 op-codes by Roger Z. T. Marty (RZTM).
	 rev 9/28/83 to incorporate changes to machine independent
	 smal and move to vax unix berkeley pascal by D. W. Jones.
	 rev 10/12/83 to conform to Rockwell standards by Roger Z. T. Marty.

	 Code not marked with <Roger Z.T. Marty's change mark> is
	 reproduced with permission of D.W. Jones. rights to further
	 reproduction of this code are reserved by D.W. Jones.

	 All portions of this code marked as altered by Roger Z.T.
	 Marty are copywrited (c) on 25 October 1983. The
	 action of reproducing, copying, or storage in any
	 retrievel system is granted as long as the name of Roger
	 Z.T. Marty is affixed to the transported code. Permission
	 is granted to alter the code in any desirable fashion as
	 long as a statment is included that the origonal code is
	 by RZTM.

	 Revised 25 October 1983 by Roger Z.T. Marty to follow Rockwell
	 International standards exactly.
     }


     { AS CURRENTLY CONFIGURED, THIS PROGRAM MUST BE RUN INTERACTIVELY;
	WHEN RUN, IT WILL REQUEST A FILE NAME FROM THE TERMINAL.  IT
	WILL THEN ASSEMBLE THAT FILE, PLACING THE LISTING ON A FILE
	NAMED THE SAME, BUT WITH A .lst SUFFIX.  OBJECT CODE IS GENERATED
	SIMILARLY ON A FILE WITH A .obj SUFFIX. 		     }

     { THIS ASSEMBLER IS WRITTEN ASSUMING THAT IT WILL RUN ON A
	MACHINE WITH AT LEAST 16 BIT TWO'S COMPLEMENT INTEGERS.   }

const
      symsize  = 1000   { NUMBER OF SYMBOLS ALLOWED IN SYMBOLTABLE };
      opcodes  = 300    { OPCODES AND MACRO NAMES ALLOWED IN OPTAB };
      poolsize = 10000  { CHARS IN STRINGPOOL; SHOULD BE GREATER THAN
			  THE AVERAGE SYMBOL LENGTH TIMES SYMSIZE, PLUS
			  THE AVERAGE OPCODE OR MACRO NAME LENGTH TIMES
			  OPCODES, PLUS ADDITIONAL SPACE FOR MACRO TEXT
			  STORAGE, PLUS ADDITIONAL SPACE FOR THE MACRO
			  CALL STACK, AT A MINIMUM OF 8 CHARACTERS PER
			  MACRO NESTING LEVEL, IF NO PARAMETERS ARE
			  PASSED. NOTE: POOLSIZE MUST NOT BE INCREASED
			  ABOVE 32767 UNLESS APPROPRIATE CHANGES ARE
			  MADE TO PUSHINT AND POPINT         };

      { These added by RZTM }
      addrmode = 13; { How many addressing modes has the micro? }
      mnemonic = 56; { How many mnemonics has the 6502 }
      ilop = 33; { Any illegal opcode. }

      { Addressing modes added by RZTM }
      zp  = 1;  { Zero Page }
      abs = 2;  { Absolute Addressing }
      imm = 3;  { Immedate Addressing }
      ac  = 4;  { Accumulator }
      imp = 5;  { Implied Addressing }
      rel = 6;  { Relative Addressing }
      x   = 7;  { Absolute Indexed X }
      y   = 8;  { Absolute Indexed Y }
      zpx = 9;  { Zero Page Indexed X }
      zpy = 10; { Zero Page Indexed Y }
      inx = 11; { Indexed X Indirect }
      iny = 12; { Indirect Indexed Y }
      ind = 13; { Indirect }

      relsym = 1   { OFFSET OF NULL SYMBOL IN POOL };
      abssym = 0   { OFFSET FOR ABS SYMBOL (JUST BELOW POOL };
      pooldel = bell{ POOL DELIMITER, AN ILLEGAL CHARACTER IN PROGRAMS,
		       SHOULD BE A NON-PRINTING CHARACTER SUCH AS NULL OR
		       DEL };
      maxgetl = 3   { NUMBER OF FILES IN INPUT FILE STACK
		       CHANGES TO THIS REQUIRE CHANGING THE NUMBER OF FILES
		       IN THE INPUT STACK (INP1, INP2, AND INP3) AND CHANGING
		       ALL CASE STATEMENTS WHICH SELECT AMONG THESE };
      parmlim = 8   { NUMBER OF MACRO PARAMETERS PER CALL.
		       NOTE: INCREASING THIS ABOVE 9 WILL REQUIRE CHANGES
		       TO ONEPASS.GETLINE.GETMAC AND TO ONEPASS.MACDEF.GETBODY;
		       THESE CURRENTLY USE DECIMAL DIGITS TO ENCODE PARAMETER
		       NUMBERS, AND MUST BE CHANGED TO USE SOME OTHER SCHEME};
      linelen = 81  { ONE MORE THAN LENGTH OF ALLOWED INPUT LINE };
      listcol = 24  { LAST COLUMN OF LISTING USED FOR OBJECT CODE INFO, SHOULD
		       SET IT SO THAT: (LISTCOL + LINELEN + 1)<(PAGE WIDTH).
		       NOTE THAT IF LISTCOL IS CHANGED TO BE LESS THAN 24, THE
		       ERROR MESSAGES MUST ALL BE SHORTENED TO KEEP THE ERROR
		       MARKUP UNDER THE RIGHT PLACES ON THE INPUT LINE.     };
      listcodes = 4 { OBJECT CODE ITEMS (BYTES,WORDS) LISTED ON A LINE, SET SO
		       THAT: ((4       * LISTCODES) + 14) > LISTCOL };
      linesper = 56 { lines per page on the listing device };
      filelen = 40  { characters per textual file name };
      pathbrk = '/' { break character in file system path names.  used for
		       implementation of USE in hierarchic file systems.
		       it is assumed in procedure insert that path names
		       starting with pathbrk are absolute, while those starting
		       with other characters are relative };


type byte = 0..255;

     symptr = 0..symsize;
     opptr = 0..opcodes;

     { file name management types }
     filename = packed array [1..filelen] of char;

     { input line buffer types }
     linebuf = packed array [1..linelen] of char;
     inbufptr = 0..linelen;

     { SYMBOLTABLE TYPES }
     poolref = 0..poolsize { REFERENCE TO A LOCATION IN THE STRING POOL };
     value = record
		  base:poolref { SYMBOL FROM WHICH VALUE IS BASED };
		  offset:integer { OFFSET FROM THAT SYMBOL };
	     end;
     association = record
		      { FIELDS KNOWN ONLY TO LOOKUP ROUTINE }
		      id: poolref;

		      { FIELDS KNOWN ONLY BY TABLE USERS }
		      val: value;
		      use: set of (def,lab { IS IT A LABEL OR DEFINED VALUE }
				  ,intdef  { IS THE VALUE TO BE EXPORTED }
				  ,usedyet { HAS VALUE BEEN USED THIS PASS }
				  ,setyet  { HAS VALUE BEEN SET THIS PASS }
				  );
		   end { RECORD };

     { OPCODE TYPES }
     optypes = (operr  { ERROR }

	       { ASSEMBLER DIRECTIVES }
	       ,opb    { BYTE CONSTANT }
	       ,opw    { WORD CONSTANT }
	       ,opascii{ TEXT CONSTANT }
	       ,opif   { CONDITIONAL ASSEMBLY }
	       ,opelseif
	       ,opelse
	       ,opendif
	       ,opint  { INTERNAL SYMBOL DEFINITION }
	       ,opext  { EXTERNAL SYMBOL DECLARATION }
	       ,opcomon{ COMMON DECLARATION }
	       ,opmac  { MACRO DECLARATION }
	       ,opendm
	       ,opuse  { USE TEXT FROM SECONDARY SOURCE }
	       ,oplist { LISTING CONTROL DIRECTIVE }
	       ,opttl  { title directive }
	       ,opsbttl{ subtitle directive }
	       ,opeject{ page eject directive }
	       ,opend  { END OF FILE }

	       { MACRO CALL TYPE }
	       ,opmcall{ MACRO CALL }

	       { MACHINE INSTRUCTION TYPES }
	       { The machine instruction types were added by
		  Roger Z.T. Marty for the 6502. }
	       ,opabs    { Absolute and all except Relative }
	       ,oprel    { Relative }
	       );

     { TYPE USED FOR PARAMETERS TO HEX PROCEDURE (FOR HEX CONSTANTS) }
     hexconst = packed array[1..4]of char;

var
    { THE FOLLOWING CONSTANT IS USED FOR REPRESENTATION INDEPENDANT
       CHARACTER CODE TRANSLATION, IT CAN BE REPLACED WITH THE ORD FUNCTION
       ON ASCII IMPLEMENTATIONS OF PASCAL       			  }
    ascii: array [char] of 0..127;

    { ALL TEXTUAL INFORMATION STORED BY THE ASSEMBLER IS IN THE STRING POOL }
    strpool: packed array [relsym..poolsize] of char;

    { TWO DATA STRUCTURES SHARE THE STRING POOL: PERMANENT TEXT GROWS UP
       FROM RELSYM, THE LAST USED LOCATION IS POINTED TO BY     	     }
    poolpos: poolref;

    { TRANSIENT TEXT GROWS DOWN FROM POOLSIZE, ORGANIZED AS A STACK.  THE
       FORMAT OF EACH STACK ENTRY IS DOCUMENTED IN ONEPASS.PUSHGET           }

    { WHEN THE STRINGPOOL FILLS UP, IT IS INDICATED BY: 		    }
    poolfull: boolean;

    { SOME KEY-WORDS ARE STORED IN THE POOL BUT NOT IN ANY SYMBOL TABLE;
       THESE ARE POINTED TO BY THE FOLLOWING (CONSTANT) VARIABLES            }
    funcdf,funcfw,functy,funcle: poolref { FUNCTION NAMES };
    funchi,funclo: poolref { More Function names, added by RZTM };

    { THE ASSEMBLER SYMBOL TABLE FOR LABELS ETC }
    symtab: array [1..symsize] of association;
    symfull: boolean { FLAG INDICATING SYMBOL TABLE IS FULL };

    { THE ASSEMBLER SYMBOL TABLE FOR OPCODES, DIRECTIVES, AND MACRO NAMES }
    optab: array [1..opcodes] of record
				    id:poolref;
				    typ:optypes;
				    val:integer;
				 end { RECORD };
    opfull: boolean { FLAG INDICATING OPCODE TABLE IS FULL };

    mnemtab: array [1..mnemonic,1..addrmode] of byte;
    { To hold the actual opcodes. The opcodes in OPINIT are row
       indices. MNEMTAB added by RZTM. }

    { textual names of input and output files }
    lstfile, objfile: filename;
    infile: array [1..maxgetl] of filename;
    inp1,inp2,inp3: text { shallow stack of source files };
    obj: text { object code file };

    { title and subtitle buffers for listing }
    titlebuf,sbttlbuf: linebuf;
    titlelen,sbttllen: inbufptr;
    lineonpg: integer { used to determine when to print title };


{ inside smal, procedure to initialize ascii translation array }

    procedure initascii;
    type string = packed array[1..16] of char;
	procedure initrow(row:integer;text:string;cnt:integer);
	var i:1..16;
	begin
	     for i := 1 to cnt do ascii[text[i]] := (row * 16) + i - 1;
	end;
    begin
	 initrow(2,' !"#$%&''()*+,-./',16);
	 initrow(3,'0123456789:;<=>?',16);
	 initrow(4,'@ABCDEFGHIJKLMNO',16);
	 initrow(5,'PQRSTUVWXYZ[\]^_',16);
	 initrow(6,'`abcdefghijklmno',16);
	 initrow(7,'pqrstuvwxyz{|}~ ',15);
	 { on machines with a smaller character set, just kill rows 6 and 7 }
    end { initascii };


{ INSIDE SMAL, FUNCTION TO IMPLEMENT CONSTANTS IN BASE 16 }

    function tohex(c:hexconst):integer;
    var i:0..4;
	acc:integer;
	digit:0..15;
    begin
	 acc := 0;
	 for i := 1 to 4 do begin
	      if c[i] in ['0'..'9']
		then digit := ord(c[i])-ord('0')
		else if c[i] in ['A'..'F']
		       then digit := (ord(c[i])-ord('A'))+10;
	      if acc > 2047 then acc := acc - 4096;
	      acc := (16*acc) + digit;
	 end;
	 tohex := acc;
    end { HEX };


{ INSIDE SMAL, FUNCTIONS SIMULATING 16 BIT TWO'S COMPLEMENT MACHINE
		 FOR EFFICIENCY, ALL OF THESE MAY BE RE-IMPLEMENTED
		 AS EXTERNAL ASSEMBLY LANGUAGE ROUTINES 	     }

    function add(i,j:integer):integer;
    begin
	 if (i > 0) and (j > 0) then begin
	      if i <= (32767 - j)
		   then add := i + j
		   else add := ((i-32767)-1) + ((j-32767)-1);
	 end else if (i < 0) and (j < 0) then begin
	      if i >= (((-32767)-1)-j)
		   then add := i + j
		   else add := ((i+32767)+1) + ((j+32767)+1);
	 end else add := i + j;
    end { ADD };

    function neg(i:integer):integer;
    begin
	 if i = ((-32767)-1)
	   then neg := ((-32767)-1)
	   else neg := -i;
    end { NEG };

    function sub(i,j:integer):integer;
    begin
	 sub := add(i,neg(j));
    end { SUB };

    function mod10(i:integer):integer;
    begin
	 if i >= 0
	   then mod10 := i mod 10
	   else mod10 := (((i + 32767 + 1) mod 10) + 8) mod 10;
    end { MOD10 };

    function div10(i:integer):integer;
    begin
	 if i >= 0
	   then div10 := i div 10
	   else div10 := ((i + 32767 + 1) div 10) + 3276
		       + ((mod10(i + 32767 + 1) + 8) div 10);
    end { DIV10 };

    function inot(i:integer):integer;
    begin
	 inot := add(neg(i),-1);
    end { INOT };

    function iand(i,j:integer):integer;
    var k,l:integer;
    begin
	 if (i<0) and (j<0) then k:=(-32767)-1 else k:=0;
	 if (i<0) then i := i + 32767 + 1;
	 if (j<0) then j := j + 32767 + 1;
	 if odd(i) and odd(j) then k := k + 1;
	 l := 1;
	 while l<16384 do begin
	      i := i div 2;
	      j := j div 2;
	      l := l  *  2;
	      if odd(i) and odd(j) then k := k + l;
	 end;
	 iand := k;
    end { IAND };

    function ior(i,j:integer):integer;
    begin
	 ior := inot(iand( inot(i) , inot(j) ));
    end { IOR };


{ INSIDE SMAL, PROCEDURES FOR DOING OUTPUT FORMAT CONVERSION }

    procedure writehex( var f:text; v,l:integer);
    { WRITE V AS AN L DIGIT HEX NUMBER ON FILE F }
    var digits: array[1..4] of char;
	digit:  0..15;
	i:      integer;
    begin
	 for i := 5 to l do write(f,' ');
	 if l > 4 then l := 4;
	 for i := 1 to l do begin
	      if v < 0 then begin
		   v := v + 32767 + 1;
		   digit := v mod 16;
		   v := (v div 16) + 2048;
	      end else begin
		   digit := v mod 16;
		   v := v div 16;
	      end;
	      if digit < 10
		then digits[i] := chr(digit + ord('0'))
		else digits[i] := chr((digit - 10) + ord('A'));
	 end;
	 for i := l downto 1 do write(f,digits[i]);
    end { WRITEHEX };

    procedure writesym(var f:text; pos:poolref);
    { WRITE THE SYMBOL FROM THE SYMBOLTABLE ON THE INDICATED FILE }
    begin
	 while strpool[pos] <> pooldel do begin
	      write(f,strpool[pos]);
	      pos := pos + 1;
	 end;
    end { WRITESYM };

    procedure genval( siz,offset:integer; base:poolref );
    { GENERATE VALUE IN OBJECT FILE BASED ON INDICATED
       SYMBOL WITH THE GIVEN OFFSET FROM THAT SYMBOL }
    begin
	 if base = abssym then begin
	      write(obj,'$');
	      writehex(obj,offset,2*siz);
	 end else begin
	      if offset = 0 then begin
		   write(obj,' ');
	      end else begin
		   write(obj,'$');
		   writehex(obj,offset,2*siz);
		   write(obj,'+');
	      end;
	      write(obj,'R');
	      writesym(obj,base);
	 end;
	 writeln(obj);
    end { GENVAL };


{ INSIDE SMAL, PROCEDURES FOR SYMBOL TABLE MANAGEMENT }

    procedure clearsym;
    { INITIALIZE ALL ENTRIES IN THE SYMBOL TABLE TO UNUSED }
    var i: symptr;
    begin
	 symfull := false;
	 for i := 1 to symsize do with symtab[i] do begin
	      id := 0;
	      use := [];
	 end;
    end { CLEARSYM };

    procedure clearuse;
    { CLEAR SYMBOL TABLE FLAGS IN PREPARATION FOR ONE PASS }
    var sym:symptr;
    begin
	 for sym := 1 to symsize do with symtab[sym] do begin
	      use := use - [usedyet,setyet];
	 end;
    end { CLEARUSE };

    procedure objsufx;
    { GENERATE SUFFIX TO OBJECT FILE WHICH DEFINES ALL INTERNAL SYMBOLS }
    var sym:symptr;
    begin
	 for sym := 1 to symsize do with symtab[sym] do begin
	      if intdef in use then begin
		   write(obj,'R');
		   writesym(obj,id);
		   write(obj,'=');
		   genval(2,val.offset,val.base);
	      end;
	 end;
    end { OBJSUFX };

    procedure opinit;
    { INITIALIZE THE OPCODE TABLE AND STRING POOL (DONE ONLY ONCE) }
    type string = packed array [1..8] of char;
    var i: opptr;
	j, k : integer;

	function putpool(s:string):poolref;
	var i: 1..8;
	begin
	     poolpos := poolpos + 1;
	     putpool := poolpos;
	     for i := 1 to 8 do if s[i]<>' ' then begin
		  strpool[poolpos] := s[i];
		  poolpos := poolpos + 1;
	     end;
	     strpool[poolpos] := pooldel;
	end { PUTPOOL };

	function hash(s:string):opptr;
	{ IT IS CRITICAL THAT THIS HASH FUNCTION MATCH THAT INSIDE ONEPASS }
	var i:1..8;
	    acc:opptr;
	begin
	     acc := 1;
	     for i := 1 to 8 do if s[i]<>' '
	       then acc := (((acc*5) + ord(s[i])) mod opcodes) + 1;
	     hash := acc;
	end { HASH };

	procedure op(s:string; t:optypes; v:integer);
	begin
	     i := hash(s);
	     while optab[i].id <> 0 do i := (i mod opcodes) + 1;
	     optab[i].id := putpool(s);
	     optab[i].typ := t;
	     optab[i].val := v;
	end { OP };

    begin { OPINIT };
	 for i := 1 to opcodes do optab[i].id := 0;
	 poolfull := false;
	 opfull := false;
	 poolpos := relsym;
	 strpool[poolpos] := pooldel;
	 { NULL SYMBOL AT START OF POOL IS DEFAULT RELOCATION BASE }
	 op('B       ',opb      ,0);
	 op('W       ',opw      ,0);
	 op('ASCII   ',opascii  ,0);
	 op('IF      ',opif     ,0);
	 op('ELSEIF  ',opelseif ,0);
	 op('ELSE    ',opelse   ,0);
	 op('ENDIF   ',opendif  ,0);
	 op('INT     ',opint    ,0);
	 op('EXT     ',opext    ,0);
	 op('COMMON  ',opcomon  ,0);
	 op('MACRO   ',opmac    ,0);
	 op('ENDMAC  ',opendm   ,0);
	 op('USE     ',opuse    ,0);
	 op('LIST    ',oplist   ,0);
	 op('TITLE   ',opttl    ,0);
	 op('SUBTITLE',opsbttl  ,0);
	 op('PAGE    ',opeject  ,0);
	 op('END     ',opend    ,0);

	 { The mnemonics for the 6502 were added by Roger Z.T.
	    Marty on 9 May 1982. There are 56 of them. }
	    { Add Memory to Accumulator with Carry }
	 op('ADC     ',opabs    ,1);
	    { AND Memory with Accumulator }
	 op('AND     ',opabs    ,2);
	    { Shift Left One Bit (Memory or Accumulator) }
	 op('ASL     ',opabs    ,3);
	    { Branch on Carry Clear }
	 op('BCC     ',oprel    ,4);
	    { Branch on Carry Set }
	 op('BCS     ',oprel    ,5);
	    { Branch on Result Zero }
	 op('BEQ     ',oprel    ,6);
	    { Test Bits in Memory with Accumulator }
	 op('BIT     ',opabs    ,7);
	    { Branch on Result Minus }
	 op('BMI     ',oprel    ,8);
	    { Branch on Result Not Zero }
	 op('BNE     ',oprel    ,9);
	    { Branch on Result Plus }
	 op('BPL     ',oprel    ,10);
	    { Force Break }
	 op('BRK     ',opabs    ,11);
	    { Branch on Overflow Clear }
	 op('BVC     ',oprel    ,12);
	    { Branch on Overflow Set }
	 op('BVS     ',oprel    ,13);
	    { Clear Carry Flag }
	 op('CLC     ',opabs    ,14);
	    { Clear Decimal Mode }
	 op('CLD     ',opabs    ,15);
	    { Clear Interupt Disable Bit }
	 op('CLI     ',opabs    ,16);
	    { Clear Overflow Flag }
	 op('CLV     ',opabs    ,17);
	    { Compare Memory and Accumulator }
	 op('CMP     ',opabs    ,18);
	    { Compare Memory and Index X }
	 op('CPX     ',opabs    ,19);
	    { Compare Memory and Index Y }
	 op('CPY     ',opabs    ,20);
	    { Decrement Memory by One }
	 op('DEC     ',opabs    ,21);
	    { Decrement Index X by One }
	 op('DEX     ',opabs    ,22);
	    { Decriment Index Y by One }
	 op('DEY     ',opabs    ,23);
	    { Exclusive-OR Memory with Accumulator }
	 op('EOR     ',opabs    ,24);
	    { Increment Memory by One }
	 op('INC     ',opabs    ,25);
	    { Increment Index X by One }
	 op('INX     ',opabs    ,26);
	    { Incriment Index Y by One }
	 op('INY     ',opabs    ,27);
	    { Jump to New Location }
	 op('JMP     ',opabs    ,28);
	    { Jump to New Location Saving Return Address }
	 op('JSR     ',opabs    ,29);
	    { Load Accumulator with Memory }
	 op('LDA     ',opabs    ,30);
	    { Load Index X with Memory }
	 op('LDX     ',opabs    ,31);
	    { Load Index Y with Memory }
	 op('LDY     ',opabs    ,32);
	    { Shift Right One Bit (Memory or Accumulator) }
	 op('LSR     ',opabs    ,33);
	    { No Operation }
	 op('NOP     ',opabs    ,34);
	    { OR Memory with Accumulator }
	 op('ORA     ',opabs    ,35);
	    { Push Accumulator on Stack }
	 op('PHA     ',opabs    ,36);
	    { Push Processor Status on Stack }
	 op('PHP     ',opabs    ,37);
	    { Pull Accumulator from Stack }
	 op('PLA     ',opabs    ,38);
	    { Pull Processor Status from Stack }
	 op('PLP     ',opabs    ,39);
	    { Rotate One Bit Left (Memory or Accumulator) }
	 op('ROL     ',opabs    ,40);
	    { Rotate One Bit Right (Memory or Accumulator) }
	 op('ROR     ',opabs    ,41);
	    { Return from Interupt }
	 op('RTI     ',opabs    ,42);
	    { Return from Subroutine }
	 op('RTS     ',opabs    ,43);
	    { Subtract Memory from Accumulator with Borrow }
	 op('SBC     ',opabs    ,44);
	    { Set Carry Flag  }
	 op('SEC     ',opabs    ,45);
	    { Set Decimal Flag }
	 op('SED     ',opabs    ,46);
	    { Set Interupt Disable Status }
	 op('SEI     ',opabs    ,47);
	    { Store Accumulator in Memory }
	 op('STA     ',opabs    ,48);
	    { Store Index X in Memory }
	 op('STX     ',opabs    ,49);
	    { Store Index Y in Memory }
	 op('STY     ',opabs    ,50);
	    { Transfer Accumulator to Index X }
	 op('TAX     ',opabs    ,51);
	    { Transfer Accumulator to Index Y }
	 op('TAY     ',opabs    ,52);
	    { Transfer Stack Pointer to Index X }
	 op('TSX     ',opabs    ,53);
	    { Transfer Index X to Accumulator }
	 op('TXA     ',opabs    ,54);
	    { Transfer Index X to Stack Pointer }
	 op('TXS     ',opabs    ,55);
	    { Transfer Index Y to Accumulator }
	 op('TYA     ',opabs    ,56);
	 { Last mnononic added by RZTM }
	 { NOTE: WHEN ADDING TO THIS LIST, BE SURE TO ADJUST THE
	    CONSTANT 'OPCODES' TO REFLECT THE ADDITIONS; THE LOCAL
	    PROCEDURE 'OP' USED ABOVE ASSUMES THAT THE OPCODE TABLE
	    WILL ALWAYS HAVE SOME FREE SPACE.   	   }
	 funcdf := putpool('DEF     ');
	 funcfw := putpool('FWD     ');
	 functy := putpool('TYP     ');
	 funcle := putpool('LEN     ');
	 { The next two were added by Roger Z.T. Marty }
	 funchi := putpool('HI      ');
	 funclo := putpool('LOW     ');

	{ Initalize the actual opcodes. First fill with illegal
	   opcodes. All routines having to do with MNEMTAB added by
	   Roger Z.T. Marty }
	for j := 1 to mnemonic do
	   for k := 1 to addrmode do
	      mnemtab[j,k] := ilop;

       { The table can be read as, rows = mnemonic opval and
	  columns = addressing mode. The addressing modes are:
	  1.   Zero Page	      8.   Absolute Indexed Y
	  2.   Absolute 	      9.   Zero Page Indexed X
	  3.   Immediate	     10.   Zero Page Indexed Y
	  4.   Implied  	     11.   Indexed X Indirect
	  5.   Accumulator           12.   Indirect Indexed Y
	  6.   Relative 	     13.   Indirect
	  7.   Absolute Indexed X             }

       mnemtab[ 1, zp]:=tohex('0065');   mnemtab[ 1,abs]:=tohex('006D');
       mnemtab[ 1,imm]:=tohex('0069');   mnemtab[ 1,  x]:=tohex('007D');
       mnemtab[ 1,  y]:=tohex('0079');   mnemtab[ 1,zpx]:=tohex('0075');
       mnemtab[ 1,inx]:=tohex('0061');   mnemtab[ 1,iny]:=tohex('0071');
       mnemtab[ 2, zp]:=tohex('0025');   mnemtab[ 2,abs]:=tohex('002D');
       mnemtab[ 2,imm]:=tohex('0029');   mnemtab[ 2,  x]:=tohex('003D');
       mnemtab[ 2,  y]:=tohex('0039');   mnemtab[ 2,zpx]:=tohex('0035');
       mnemtab[ 2,inx]:=tohex('0021');   mnemtab[ 2,iny]:=tohex('0031');
       mnemtab[ 3, zp]:=tohex('0006');   mnemtab[ 3,abs]:=tohex('000E');
       mnemtab[ 3, ac]:=tohex('000A');   mnemtab[ 3,  x]:=tohex('001E');
       mnemtab[ 3,zpx]:=tohex('0016');   mnemtab[ 4,rel]:=tohex('0090');
       mnemtab[ 5,rel]:=tohex('00B0');   mnemtab[ 6,rel]:=tohex('00F0');
       mnemtab[ 7, zp]:=tohex('0024');   mnemtab[ 7,abs]:=tohex('002C');
       mnemtab[ 8,rel]:=tohex('0030');   mnemtab[ 9,rel]:=tohex('00D0');
       mnemtab[10,rel]:=tohex('0010');   mnemtab[11,imp]:=tohex('0000');
       mnemtab[12,rel]:=tohex('0050');   mnemtab[13,rel]:=tohex('0070');
       mnemtab[14,imp]:=tohex('0018');   mnemtab[15,imp]:=tohex('00D8');
       mnemtab[16,imp]:=tohex('0058');   mnemtab[17,imp]:=tohex('00B8');
       mnemtab[18, zp]:=tohex('00C5');   mnemtab[18,abs]:=tohex('00CD');
       mnemtab[18,imm]:=tohex('00C9');   mnemtab[18,  x]:=tohex('00DD');
       mnemtab[18,  y]:=tohex('00D9');   mnemtab[18,zpx]:=tohex('00D5');
       mnemtab[18,inx]:=tohex('00C1');   mnemtab[18,iny]:=tohex('00D1');
       mnemtab[19, zp]:=tohex('00E4');   mnemtab[19,abs]:=tohex('00EC');
       mnemtab[19,imm]:=tohex('00E0');   mnemtab[20, zp]:=tohex('00C4');
       mnemtab[20,abs]:=tohex('00CC');   mnemtab[20,imm]:=tohex('00C0');
       mnemtab[21, zp]:=tohex('00C6');   mnemtab[21,abs]:=tohex('00CE');
       mnemtab[21,  x]:=tohex('00DE');   mnemtab[21,zpx]:=tohex('00D6');
       mnemtab[22,imp]:=tohex('00CA');   mnemtab[23,imp]:=tohex('0088');
       mnemtab[24, zp]:=tohex('0045');   mnemtab[24,abs]:=tohex('004D');
       mnemtab[24,imm]:=tohex('0049');   mnemtab[24,  x]:=tohex('005D');
       mnemtab[24,  y]:=tohex('0059');   mnemtab[24,zpx]:=tohex('0055');
       mnemtab[24,inx]:=tohex('0041');   mnemtab[24,iny]:=tohex('0051');
       mnemtab[25, zp]:=tohex('00E6');   mnemtab[25,abs]:=tohex('00EE');
       mnemtab[25,  x]:=tohex('00FE');   mnemtab[25,zpx]:=tohex('00F6');
       mnemtab[26,imp]:=tohex('00E8');   mnemtab[27,imp]:=tohex('00C8');
       mnemtab[28,abs]:=tohex('004C');   mnemtab[28,ind]:=tohex('006C');
       mnemtab[29,abs]:=tohex('0020');   mnemtab[30, zp]:=tohex('00A5');
       mnemtab[30,abs]:=tohex('00AD');   mnemtab[30,imm]:=tohex('00A9');
       mnemtab[30,  x]:=tohex('00BD');   mnemtab[30,  y]:=tohex('00B9');
       mnemtab[30,zpx]:=tohex('00B5');   mnemtab[30,inx]:=tohex('00A1');
       mnemtab[30,iny]:=tohex('00B1');   mnemtab[31, zp]:=tohex('00A6');
       mnemtab[31,abs]:=tohex('00AE');   mnemtab[31,imm]:=tohex('00A2');
       mnemtab[31,  y]:=tohex('00BE');   mnemtab[31,zpy]:=tohex('00B6');
       mnemtab[32, zp]:=tohex('00A4');   mnemtab[32,abs]:=tohex('00AC');
       mnemtab[32,imm]:=tohex('00A0');   mnemtab[32,  x]:=tohex('00BC');
       mnemtab[32,zpx]:=tohex('00B4');   mnemtab[33, zp]:=tohex('0046');
       mnemtab[33,abs]:=tohex('004E');   mnemtab[33, ac]:=tohex('004A');
       mnemtab[33,  x]:=tohex('005E');   mnemtab[33,zpx]:=tohex('0056');
       mnemtab[34,imp]:=tohex('00EA');   mnemtab[35, zp]:=tohex('0005');
       mnemtab[35,abs]:=tohex('000D');   mnemtab[35,imm]:=tohex('0009');
       mnemtab[35,  x]:=tohex('001D');   mnemtab[35,  y]:=tohex('0019');
       mnemtab[35,zpx]:=tohex('0015');   mnemtab[35,inx]:=tohex('0001');
       mnemtab[35,iny]:=tohex('0011');   mnemtab[36,imp]:=tohex('0048');
       mnemtab[37,imp]:=tohex('0008');   mnemtab[38,imp]:=tohex('0068');
       mnemtab[39,imp]:=tohex('0028');   mnemtab[40, zp]:=tohex('0026');
       mnemtab[40,abs]:=tohex('002E');   mnemtab[40, ac]:=tohex('002A');
       mnemtab[40,  x]:=tohex('003E');   mnemtab[40,zpx]:=tohex('0036');
       mnemtab[41, zp]:=tohex('0066');   mnemtab[41,abs]:=tohex('006E');
       mnemtab[41, ac]:=tohex('0068');   mnemtab[41,  x]:=tohex('007E');
       mnemtab[41,zpx]:=tohex('0076');
       mnemtab[42,imp]:=tohex('0040');   mnemtab[43,imp]:=tohex('0060');
       mnemtab[44, zp]:=tohex('00E5');   mnemtab[44,abs]:=tohex('00ED');
       mnemtab[44,imm]:=tohex('00E9');   mnemtab[44,  x]:=tohex('00FD');
       mnemtab[44,  y]:=tohex('00F9');   mnemtab[44,zpx]:=tohex('00F5');
       mnemtab[44,inx]:=tohex('00E1');   mnemtab[44,iny]:=tohex('00F1');
       mnemtab[45,imp]:=tohex('0038');   mnemtab[46,imp]:=tohex('00F8');
       mnemtab[47,imp]:=tohex('0078');   mnemtab[48, zp]:=tohex('0085');
       mnemtab[48,abs]:=tohex('008D');   mnemtab[48,  x]:=tohex('009D');
       mnemtab[48,  y]:=tohex('0099');   mnemtab[48,zpx]:=tohex('0095');
       mnemtab[48,inx]:=tohex('0081');   mnemtab[48,iny]:=tohex('0091');
       mnemtab[49, zp]:=tohex('0086');   mnemtab[49,abs]:=tohex('008E');
       mnemtab[49,zpy]:=tohex('0096');   mnemtab[50, zp]:=tohex('0084');
       mnemtab[50,abs]:=tohex('008C');   mnemtab[50,zpx]:=tohex('0094');
       mnemtab[51,imp]:=tohex('00AA');   mnemtab[52,imp]:=tohex('00A8');
       mnemtab[53,imp]:=tohex('00BA');   mnemtab[54,imp]:=tohex('008A');
       mnemtab[55,imp]:=tohex('009A');   mnemtab[56,imp]:=tohex('0098');
	  { End of additions by RZTM to OPINIT }

    end { OPINIT };


{ INSIDE SMAL, MAIN ASSEMBLY PROCEDURE FOR ONE PASS THROUGH SOURCE }

    procedure onepass( firstpass,allowlist: boolean );
    {  PERFORM ONE ASSEMBLY PASS.  PRODUCE OUTPUT IF LISTING=TRUE  }

    type ermsg = (minermsg
		 ,baddir { BAD ASSEMBLY DIRECTIVE }
		 ,unfunc { BAD FUNCTION }
		 ,notlab { EXPECTED LABEL OR DIRECTIVE }
		 ,notval { EXPECTED A VALUE, GOT SOMETHING ELSE }
		 ,muldef { MULTIPLE SYMBOL DEFINITION }
		 ,fwdref { DEFINITION MUST PRECEDE USE }
		 ,phase  { PHASE ERROR IN LABEL VALUE BETWEEN PASSES }
		 ,undef  { UNDEFINED SYMBOL }
		 ,idexp  { IDENTIFIER EXPECTED }
		 ,quoexp { QUOTED STRING EXPECTED }
		 ,comexp { COMMA EXPECTED }
		 ,bounds { VALUE OUT OF BOUNDS }
		 ,baddig { BAD DIGIT IN NUMBER }
		 ,badrad { BAD RADIX }
		 ,badrel { MISUSE OF RELOCATION IN EXPRESSION }
		 ,unbal  { UNBALANCED PARENS }
		 ,misquo { MISSING END QUOTE }
		 ,parexp { PARENTHESIZED LIST EXPECTED }
		 ,maxuse { TOO MANY SOURCE FILES }
		 ,unproc { UNPROCESSED DATA AT END OF LINE }
		 ,miseif { MISSING ENDIF }
		 ,misemc { MISSING ENDMAC }
		 ,parovf { TOO MANY MACRO PARAMETERS }
		 ,notfit { TEXT TOO LONG FOR LINE }
		     { The next five added by RZTM }
		 ,notind { Expected an index, got something else }
		 ,iladdr { Illegal addressing mode }
		 ,noexis { Non-existant addressing mode }
		 ,eprexp { End paren expected }
		 ,notzp  { Vector not on Zero Page }
		 ,maxermsg);

	 { TYPES HAVING TO DO WITH LEXICAL ANALYSIS }
	 lextypes = (id       { IDENTIFIER }
		    ,num      { NUMBER (HEX OR DECIMAL) }
		    ,quote    { QUOTED STRING }
		    ,colon    { : }
		    ,dot      { . }
		    ,comma    { , }
		    ,eq       { = }
		    ,gt       { > }
		    ,lt       { < }
		    ,plus     { + }
		    ,minus    { - }
		    ,notsym   { \ }
		    ,andsym   { & }
		    ,orsym    { ! }
		    ,bpar     { ( }
		    ,epar     { ) }
		    ,poundsym { # }   { This added by rztm }
		    ,eol      { END OF LINE AND START OF COMMENT }
		    ,junk     { STRING OF UNCLASSIFIED CHARACTERS }
		    );
	 lexeme = record
		       pos,lim: inbufptr { START, END OF LEXEME IN LINE };
		       case typ: lextypes of
			num: ( val: integer { VALUE OF NUMBER }        )
		  end {RECORD};

    var letters,lowletters,quotemarks,digits,
	hexdigits,lexpunc,valid: set of char;
	{ THE ABOVE ARE SUPPOSED TO BE CONSTANTS }
	{ LOWLETTERS added by Roger Z.T. Marty }

	loc: value      { CURRENT ASSEMBLY LOCATION COUNTER };
	maxrel: integer { MAX VAL OF LOC.OFFSET WHEN LOC.BASE = RELSYM };
	objloc: value   { CURRENT OBJECT CODE GENERATION LOCATION COUNTER };
	lineno: integer { CURRENT LINE IN ASSEMBLY SOURCE };

	lex: lexeme     { CURRENT LEXEME };
	next: lexeme    { NEXT LEXEME FOR LOOKAHEAD USE };

	{ VARIABLES ASSOCIATED WITH STACK ON TRANSIENT END OF STRINGPOOL }
	poolsp: poolref       { POOL STACK POINTER };
	oldsp:  poolref       { POINTER TO PREVIOUS FRAME IN STACK };
	actcnt: 0..parmlim    { COUNT OF ACTUAL PARAMS IN CURRENT FRAME };
	actparm: array [1..parmlim] of poolref { POINTERS TO AP'S IN FRAME };

	{ VARIABLES CONTROLING SOURCE OF INPUT }
	gettext: poolref      { LOC IN POOL FROM WHICH MACRO TEXT COMES };
	getlevel: 0..maxgetl  { FILE FROM WHICH NON-MACRO TEXT COMES };

	{ LINE BUFFERS AND LEXICAL ANALYSIS }
	line: linebuf;
	pos: 1..linelen 	{ CURRENT INPUT LINE POSITION };
	length: inbufptr	{ CURRENT INPUT LINE LENGTH };

	{ RECORD OF ERRORS ON THE CURRENT LINE }
	erbuf: linebuf  	{ MARKUP UNDER ERROR };
	ermax: inbufptr 	{ MAX USED POSITION IN ERBUF };
	erset: set of ermsg     { SET OF MESSAGES TO GENERATE };

	{ RECORD OF CODE GENERATED BY CURRENT LINE }
	codebuf: array [1..listcodes] of record
				      val: value;
				      siz: 1..2;
				 end;
	codelen: 0..listcodes;
	codeloc: value;

	{ LISTING CONTROL VARIABLES }
	listing: boolean  { SET TO (LISTLEVEL > 0) AND (ALLOWLIST) };
	listlevel: integer { DEC ON MACRO CALL, INC ON RETURN };

	{ INFO ABOUT LAST EXPRESSION }
	expr:value            { VALUE OF EXPRESSION };
	exprdef:boolean 	 { IS THE VALUE OF THE EXPRESSION DEFINED };
	exprpos,exprlim:inbufptr { POSITION OF EXPRESSION ON LINE };

	{ INFO ABOUT OPCODE DECODED ON CURRENT LINE }
	optype:optypes;
	opval:integer;
	oppos,oplim:inbufptr;


    { INSIDE SMAL.ONEPASS, ROUTINES TO MANAGE STACK IN STRINGPOOL,
		     THESE ROUTINES ASSUME THAT ORD(MAXCH)>=32; IF
		     ORD(MAXCH)>32, THEY MAY BE RECODED FOR GREATER
		     EFFICIENCY WITHOUT ANY EFFECT ON THEIR USERS   }

	procedure pushchar(ch:char);
	{ PUSH ONE CHAR ONTO STACK IN STRINGPOOL }
	begin
	     if poolsp > poolpos then begin
		  strpool[poolsp] := ch;
		  poolsp := poolsp - 1;
	     end else begin
		  poolfull := true;
	     end;
	end { PUSHCHAR };

	function pushtext(pos,lim:inbufptr):poolref;
	{ PUSH THE INDICATED TEXT ONTO THE STACK FROM THE LINE,
	   AS A TERMINATED STRING, RETURN A REFERENCE TO THE FIRST CHAR }
	var i:inbufptr;
	begin
	     pushchar(pooldel);
	     for i := lim-1 downto pos do pushchar(line[i]);
	     pushtext := poolsp + 1;
	end { PUSHTEXT };

	function pushitxt(i:integer):poolref;
	{ PUSH THE INDICATED INTEGER AS A DECIMAL TEXT STRING, TERMINATED
	   WITH A POOLDEL, AND RETURN A REFERENCE TO THE FIRST CHAR }
	begin
	     pushchar(pooldel);
	     if i = 0 then begin
		  pushchar('0');
	     end else begin
		  while i <> 0 do begin
		       pushchar(chr( mod10(i) + ord('0') ));
		       i := div10(i);
		  end;
	     end;
	     pushitxt := poolsp + 1;
	end { PUSHITXT };

	function popchar:char;
	{ POP ONE CHAR FROM STACK IN STRINGPOOL }
	begin
	     poolsp := poolsp + 1;
	     popchar := strpool[poolsp];
	end { POPCHAR };

	procedure pushint(i:integer);
	{ PUSH AN INTEGER ONTO STACK AS A SEQUENCE OF CHARS }
	begin
	     pushchar(chr( i mod 32 ));
	     pushchar(chr( (i div 32) mod 32 ));
	     pushchar(chr( i div 1024 ));
	end { PUSHINT };

	function popint:integer;
	{ POP AN INTEGER FROM THE STACK AS A SEQUENCE OF CHARS }
	var i:integer;
	begin
	     i := ord(popchar) * 1024;
	     i := i + (ord(popchar) * 32);
	     popint := i + ord(popchar);
	end { POPINT };

	procedure pushget;
	{ PUSH A MACRO EXPANSION CONTROL BLOCK ON THE STACK }
	var i:1..parmlim;
	begin
	     listlevel := listlevel - 1;
	     for i := 1 to actcnt do pushint(actparm[i]);
	     pushchar(chr(actcnt));
	     pushint(oldsp);
	     pushint(gettext);
	     pushchar(chr(getlevel));
	     oldsp := poolsp;
	end { PUSHGET };

	procedure popget;
	{ POP A MACRO EXPANSION CONTROL BLOCK FROM THE STACK }
	var i:1..parmlim;
	begin
	     if poolfull then begin { CAN'T POP SAFELY, SO GO ALL THE WAY }
		  listlevel := 1;
		  gettext := 0;
		  getlevel := 0;
	     end else begin { CAN POP ONE LEVEL SAFELY }
		  listlevel := listlevel + 1;
		  poolsp := oldsp;
		  getlevel := ord(popchar);
		  gettext := popint;
		  oldsp := popint;
		  actcnt := ord(popchar);
		  for i := actcnt downto 1 do actparm[i] := popint;
	     end;
	end { POPGET };


    { INSIDE SMAL.ONEPASS, INPUT/OUTPUT ROUTINES }

	procedure error( msg: ermsg; pos,lim: inbufptr );
	{ RECORD ERROR AND POSITION OF ERROR IN LINE FOR LATER PRINTING }
	var i: inbufptr;
	begin
	     listing := allowlist { FORCE ERROR LINE TO BE LISTED };
	     erset := erset + [msg];
	     for i := ermax+1 to pos-1 do erbuf[i] := ' ';
	     for i := pos to lim-1 do erbuf[i] := '=';
	     if lim > ermax+1 then ermax := lim - 1;
	end { ERROR };

	procedure getline;
	{  READ ONE LINE FROM THE INPUT FILE, INITIALIZE THE
	    LEXICAL ANALYSIS AND LISTING CONTROL VARIABLES    }
	var i:inbufptr;
	    ch:char;

	    procedure makeend;
	    { PUT AN END DIRECTIVE ON THE LINE AS RESULT OF END FILE }
	    begin
		 line[1] := 'E';
		 line[2] := 'N';
		 line[3] := 'D';
		 i := 3;
	    end { MAKEEND };

	    procedure getmac;
	    { GET ONE LINE OF TEXT FROM THE STRING POOL COPY OF MACRO BODY }
	    var parmnum:integer;
		parm:poolref;
	    begin
		 i := 0;
		 repeat
		      ch := strpool[gettext];
		      gettext := gettext + 1;
		      while (ch <> pooldel) and (i < (linelen - 1)) do begin
			   i := i + 1;
			   line[i] := ch;
			   ch := strpool[gettext];
			   gettext := gettext + 1;
		      end { WHILE };
		      if ch <> pooldel then begin { ISN'T SPACE IN THE LINE }
			   error(notfit,0,0);
			   while strpool[gettext] <> pooldel
			     do gettext := gettext + 1;
			   gettext := gettext + 1;
		      end;
		      ch := strpool[gettext] { CHAR AFTER POOLDEL };
		      gettext := gettext + 1;
		      if ch in digits then begin { MACRO PARAMETER }
			   parmnum := ord(ch)-ord('0');
			   if parmnum <= actcnt then begin { PARAM EXISTS }
				parm := actparm[parmnum];
				if parm > 0 then begin { PARAM IS NONBLANK }
				     ch := strpool[parm];
				     while (ch <> pooldel)
				       and (i < (linelen - 1)) do begin
					  i := i + 1;
					  line[i] := ch;
					  parm := parm + 1;
					  ch := strpool[parm];
				     end { LOOP COPYING TEXT OF PARAMETER };
				     if ch <> pooldel then error(notfit,0,0);
				end;
			   end;
			   ch := ' ' { FORCE REPEAT LOOP TO CONTINUE };
		      end;
		 until ch in [',',pooldel];
		 if ch = pooldel then makeend;
	    end { GETMAC };

	    procedure get(var f:text);
	    { READ ONE LINE FROM APPROPRIATE INPUT FILE }
	    begin
		 if eof(f) then begin
		      makeend;
		 end else begin
		      i := 0;
		      while ( not(eoln(f)) )and( i<(linelen-1) ) do begin
			   i := i+1;
			   read( f, ch );
			   if ch = pooldel then ch := '@';
			   line[i] := ch;
		      end;
		      if not(eoln(f)) then error(notfit,0,0);
		      readln( f );
		 end;
	    end { GET };

	begin { GETLINE }
	     erset := [];
	     ermax := 0;
	     if gettext > 0 then begin
		  getmac
	     end else begin
		  if getlevel = 1 then lineno := lineno + 1;
		  case getlevel of
		       1: get(inp1);
		       2: get(inp2);
		       3: get(inp3);
		  end { CASE };
		  { NOTE THAT LINES ARE ONLY COUNTED AT THE BOTTOM LEVEL }
	     end;
	     length := i;
	     line[i+1] := ';' { THIS CHAR MUST BE INITIALIZED };
	     pos := 1;
	     lex.typ := eol;
	     lex.pos := 1;
	     lex.lim := 1;
	     next.typ := eol;
	     next.pos := 1;
	     next.lim := 1;
	     codelen := 0;
	end { GETLINE };

	procedure settitle( var buf:linebuf;
			    var len:inbufptr;
			    pos,lim:inbufptr );
	{ fill the indicated title buffer with the indicated part
	   of the input line    				   }
	var i:inbufptr;
	begin
	     len := 0;
	     for i := pos to lim do begin
		  len := len + 1;
		  buf[len] := line[i];
	     end;
	end { settitle };

	procedure newpage;
	{ force listing to the start of a new page }
	var ff:char;
	begin
	     if lineonpg <> 1 then begin
		  ff := chr(12) { formfeed character };
		  write(ff);
		  { note that instead of using a formfeed, this routine
		     could be written to simply output blank lines and
		     count them with lineonpg until the count was high
		     enough to push the listing to a new page   	}
		  lineonpg := 1;
	     end;
	end { newpage };

	procedure listline;
	{  list one line, including generated code.
	    if there are any errors, list the error messages  }
	var i:inbufptr;
	    msg:ermsg;
	    col,nextcol:integer { column on output listing };

	    procedure title;
	    { write title to listing file }
	    var i:inbufptr;
	    begin
		 write( 'SMAL 6502 ASSEMBLER, REV 6/20/84.   ' );
		 for i := 1 to titlelen do write( titlebuf[i] );
		 writeln;
		 write( '                                    ' );
		 for i := 1 to sbttllen do write( sbttlbuf[i] );
		 writeln;
		 writeln;
	    end { title };

	begin { listline }
	     if lineonpg = 1 then title;
	     write(lineno:6,' ');
	     col := 8;
	     if codelen > 0 then begin { list generated code }
		  if codeloc.base = abssym then write(' ') else write('+');
		  writehex( output, codeloc.offset,4 );
		  write(':');
		  col := 14;
		  i := 0;
		  while i < codelen do begin { list each code item }
		       i := i + 1;
		       with codebuf[i] do begin
			    nextcol := col + siz + siz + 2;
			    if nextcol > listcol then begin
				 i := codelen;
			    end else begin
				 if val.base=abssym
				   then write(' ')
				   else write('+');
				 writehex(output,val.offset,2*siz);
				 write(' ');
				 col := nextcol;
			    end;
		       end { with };
		  end { while };
	     end { listing of generated code };
	     for col := col to listcol do write(' ');
	     { text starts in column listcol + 1 }
	     write(']');
	     for i := 1 to length do write(line[i]);
	     { write out all accumulated error messages }
	     if erset <> [] then begin
		  for msg := minermsg to maxermsg do if msg in erset then begin
		       writeln;
		       lineonpg := lineonpg + 1;
		       if lineonpg > linesper then begin
			    newpage;
			    title;
		       end;
		       case msg of
			 baddir: write('INVALID DIRECTIVE        ');
			 unfunc: write('INVALID FUNCTION         ');
			 notlab: write('NOT A LABEL OR DIRECTIVE ');
			 notval: write('BAD VALUE OR EXPRESSION  ');
			 muldef: write('MULTIPLE LABEL DEFINITION');
			 fwdref: write('NAME USED BEFORE DEFINED ');
			 phase:  write('LABEL DIFFERED IN PASS 1 ');
			 undef:  write('UNDEFINED SYMBOL         ');
			 idexp:  write('SYMBOLIC NAME EXPECTED   ');
			 quoexp: write('QUOTED STRING EXPECTED   ');
			 comexp: write('COMMA EXPECTED           ');
			 bounds: write('VALUE OUT OF BOUNDS      ');
			 baddig: write('BAD DIGIT IN NUMBER      ');
			 badrad: write('BAD RADIX                ');
			 badrel: write('MISUSE OF RELOCATION     ');
			 unbal:  write('UNBALANCED PARENTHESES   ');
			 misquo: write('MISSING END QUOTE        ');
			 parexp: write('NOT A PARENTHESIZED LIST ');
			 maxuse: write('TOO MANY USE LEVELS      ');
			 unproc: write('COMMENT OR EOL EXPECTED  ');
			 miseif: write('MISSING ENDIF            ');
			 misemc: write('MISSING ENDMAC           ');
			 parovf: write('TOO MANY MACRO PARAMETERS');
			 notfit: write('TEXT TOO LONG FOR LINE   ');
			    { Next five added by RZTM }
			 iladdr: write('ILLEGAL ADDRESSING MODE  ');
			 noexis: write('NON-EXISTANT ADDRESS MODE');
			 eprexp: write('END PARENTHESIS EXPECTED ');
			 notind: write('INDEX EXPECTED           ');
			 notzp:  write('VECTOR NOT ON ZERO PAGE  ')
		       end { case };
		       for col := 26 to listcol+1 do write(' ');
		       for i := 1 to ermax do write( erbuf[i] );
		       ermax := 0;
		  end { for };
	     end { if };
	     writeln;
	     lineonpg := lineonpg + 1;
	     if lineonpg >= linesper then newpage;
	end { listline };

	procedure putobj( siz,offset:integer; base:poolref );
	{  STORE SIZ BYTES IN CURRENT LOC.
	    ADVANCE LOC BY SIZE, GENERATE OBJECT CODE AND LISTING }
	begin
	     if allowlist then begin
		  { FIRST ASSURE THAT CODE GETS LOADED IN RIGHT LOC }
		  if (objloc.offset <> loc.offset) or (objloc.base <> loc.base)
		    then begin
		       objloc := loc;
		       write(obj,'.=');
		       genval(2,loc.offset,loc.base);
		  end;
		  { THEN GENERATE CORRECT OBJECT CODE }
		  case siz of
		       1: write(obj,'B');
		       2: write(obj,'W')
		  end;
		  genval(siz,offset,base);
		  objloc.offset := objloc.offset + siz;
		  { FINALLY GENERATE APPROPRIATE LISTING DATA }
		  if codelen=0 then codeloc := loc;
		  if codelen < listcodes then begin
		       codelen := codelen + 1;
		       codebuf[codelen].val.offset := offset;
		       codebuf[codelen].val.base := base;
		       codebuf[codelen].siz := siz;
		  end;
	     end;
	     loc.offset := loc.offset + siz;
	end { PUTOBJ };

	procedure putascii(pos,lim:inbufptr);
	{ GENERATE OBJECT CODE FOR ASCII STRING }
	var i:inbufptr;
	begin
	     for i := pos to lim-1 do putobj(1,ascii[line[i]],abssym);
	end;


    { INSIDE SMAL.ONEPASS, LEXICAL ANALYSIS ROUTINES }

	procedure nextlex;
	{  SAVE THE NEXT LEXEME INFORMATION IN THE CURRENT LEXEME
	    VARIABLE, THEN READ A NEW NEXT ONE FROM THE INPUT LINE }
	var ch:char;
	    mark:char;

	    function number( radix: integer ): integer;
	    var acch,accl: integer   { ACCUMULATES THE VALUE };
		digit: integer       { THE VALUE OF ONE DIGIT };
	    begin
		 { ASSUME INITIALLY THAT CH IS A VALID DIGIT }
		 acch := 0;
		 accl := 0;
		 repeat
		      if ch in digits
			then digit := ord(ch) - ord('0')
			else digit := 10 + (ord(ch) - ord('A'));
		      if digit >= radix then begin
			   ch := 'Z';
			   acch := 256;
		      end else begin
			   pos := pos + 1;
			   ch := line[pos];
			   accl := (accl * radix) + digit;
			   acch := (acch * radix) + (accl div 256);
			   accl := accl mod 256;
		      end;
		 until not(ch in (letters+digits)) or (acch >= 256);
		 if ch in letters then begin
		      while ch in (letters+digits) do begin
			   pos := pos + 1;
			   ch := line[pos];
		      end;
		      error(baddig,next.pos,pos);
		      number := 0;
		 end else if acch >= 256 then begin
		      while ch in (letters+digits) do begin
			   pos := pos + 1;
			   ch := line[pos];
		      end;
		      error(bounds,next.pos,pos);
		      number := 0;
		 end else if acch >= 128 then begin
		      number := (-32767-1) + (256 * (acch - 128)) + accl;
		 end else begin
		      number := (256 * acch) + accl;
		 end;
	    end { NUMBER };

	begin { NEXTLEX }
	     lex := next;
	     while (line[pos]=' ') do pos := pos+1;
	     ch := line[pos];
	     next.pos := pos;
	     if ch = ';' then begin
		  next.typ := eol;
	     end else if ch in lexpunc then begin
		  case ch of
		       ':': next.typ := colon;
		       '.': next.typ := dot;
		       ',': next.typ := comma;
		       '=': next.typ := eq;
		       '>': next.typ := gt;
		       '<': next.typ := lt;
		       '+': next.typ := plus;
		       '-': next.typ := minus;
		       '\': next.typ := notsym;
		       '&': next.typ := andsym;
		       '!': next.typ := orsym;
		       '#': next.typ := poundsym;  { This added by RZTM }
		       '(': next.typ := bpar;
		       ')': next.typ := epar
		  end { CASE };
		  pos := pos+1;
	     end else if ch in digits then begin
		  next.typ := num;
		  next.val := number(10);
		  if ch in ['$','@','%'] then begin
		       if (next.val > 36) or (next.val < 2) then begin
			    next.val := 36;
			    error(badrad,next.pos,pos);
		       end;
		       pos := pos + 1;
		       ch := line[pos];
		       if ch in (letters+digits)
			 then next.val := number(next.val)
			 else error(baddig,next.pos,pos);
		  end;
	     { LOWLETTERS added by RZTM }
	     end else if ch in (letters + lowletters) then begin
		  next.typ := id;
		  { The next two lines were added by RZTM }
		  if (ch in lowletters) then
		       line[pos] := chr(ord(ch) - (ord('a')-ord('A')));
		  repeat
		       pos := pos+1;
		       ch := line[pos];
		       { The next two lines were added by RZTM }
		       if (ch in lowletters) then
			  line[pos] := chr(ord(ch) - (ord('a')-ord('A')));
		  until not(ch in (digits + lowletters + letters + ['_']));
		  { Underscore and LOWLETTERS added by RZTM }
		  { To add dot as a delimiter in variable names,
		     change '(DIGITS + LETTERS + LOWLETTERS + ['_'])' TO
			    '(DIGITS + LETTERS + ['_'] + ['.'])'  }
	     end else if ch in ['$','@','%'] then begin
		  case ch of
		     '$': next.val := 16;
		     '@': next.val := 8;
		     '%': next.val := 2;
		  end;
		  pos := pos + 1;
		  ch := line[pos];
		  if ch in hexdigits then begin
		       next.typ := num;
		       next.val := number(next.val);
		  end else begin
		       next.typ := junk;
		  end { if };
	     end else if ch in quotemarks then begin
		  mark := ch;
		  next.typ := quote;
		  repeat
		       pos := pos + 1;
		  until (line[pos] = mark) or (pos > length);
		  if pos <= length then begin
		       pos := pos + 1;
		  end else begin
		       error(misquo,next.pos,next.pos+1);
		  end;
	     end else begin { INVALID LEXEME }
		  repeat
		       pos := pos+1;
		       ch := line[pos];
		  until ch in valid;
		  next.typ := junk;
	     end;
	     next.lim := pos;
	end { NEXTLEX };

	procedure startup;
	{ SETUP FOR PROCESSING ONE LINE OF INPUT }
	begin
	     getline { READ INPUT LINE };
	     nextlex { READ FIRST LEXEME };
	     nextlex { READ SECOND LEXEME (ALLOW LOOKAHEAD) };
	     { START PARSING BY LOOKING FOR VALID START OF LINE }
	     while not(lex.typ in [id,eol,dot]) do begin
		  error(notlab,lex.pos,lex.lim);
		  nextlex;
	     end;
	end { STARTUP };

    { INSIDE SMAL.ONEPASS, STRING POOL AND SYMBOL TABLE MANAGEMENT }

	procedure putch( ch:char );
	{ PUT ONE CHAR INTO PERMANENT END OF STRINGPOOL }
	begin
	     if poolsp > poolpos then begin { THERE IS ROOM IN POOL }
		  poolpos := poolpos + 1;
		  strpool[poolpos] := ch;
	     end else begin { THERE ISN'T ROOM }
		  poolfull := true;
	     end;
	end { PUTCH };

	function putpool( pos,lim:inbufptr ): poolref;
	{ PUT THE STRING BETWEEN POS AND LIM-1 ON THE CURRENT LINE INTO
	   THE STRING POOL, RETURNING IT'S INDEX IN THE POOL.  THE STRING
	   DELIMITER IS APPENDED TO THE STRING IN THE POOL.  IT IS ASSUMED
	   THAT THE STRING WILL FIT (THE CALLER MUST GUARANTEE THIS)    }
	var i:inbufptr;
	begin
	     poolpos := poolpos + 1;
	     putpool := poolpos;
	     for i := pos to lim-1 do begin
		  strpool[poolpos] := line[i];
		  poolpos := poolpos + 1;
	     end;
	     strpool[poolpos] := pooldel;
	end { PUTPOOL };

	function poolfit(pos,lim: inbufptr): boolean;
	{ CHECK TO SEE IF TEXT BETWEEN POS AND LIM WILL FIT IN STRINGPOOL }
	begin
	     poolfit := ( (poolsp - poolpos) > (lim - pos) );
	end { POOLFIT };

	function poolcmp( poolpos:poolref; pos,lim:inbufptr ):boolean;
	{ COMPARE THE STRING STARTING AT POOLPOS IN THE STRINGPOOL WITH
	   THAT BETWEEN POS AND LIM ON THE CURRENT LINE, RETURN TRUE IF
	   THEY ARE THE SAME; THIS RELIES ON THE FACT THAT THE STRING
	   DELIMITER IN THE STRINGPOOL WILL NEVER OCCUR IN THE LINE   }
	begin
	     while strpool[poolpos] = line[pos] do begin
		  poolpos := poolpos + 1;
		  pos := pos + 1;
	     end;
	     poolcmp := (strpool[poolpos] = pooldel) and (pos = lim);
	end { POOLCMP };

	function hash( pos,lim: inbufptr; modulus: integer): integer;
	{ COMPUTE HASH OF LEXEME BETWEEN POS AND LIM,
	   RETURN A VALUE BETWEEN 1 AND MODULUS (INCLUSIVE)
	   THIS HASH FUNCTION MUST MATCH THAT IN "OPINIT"  }
	var acc: integer;
	    p: inbufptr;
	begin
	     acc := 1;
	     for p := pos to lim-1
	       do acc := (((acc*5) + ord(line[p])) mod modulus) + 1;
	     hash := acc;
	end { HASH };

	function lookup( pos,lim: inbufptr ): symptr;
	{ FIND THE SYMBOL BETWEEN POS AND LIM ON THE CURRENT LINE IN
	   THE SYMBOL TABLE, RETURN THE INDEX INTO THE TABLE WHERE IT
	   WAS FOUND OR INSERTED; IF IT COULD NOT BE INSERTED, RETURN
	   ZERO 						     }
	var s,olds: symptr;
	begin
	     s := hash(pos,lim,symsize);
	     olds := s;
	     lookup := 0 { DEFAULT RETURN VALUE };
	     repeat
		  with symtab[s] do begin
		       if id<>0 then begin
			    if poolcmp(id,pos,lim) then begin
				 lookup := s;
				 s := olds  { TERMINATE LOOP };
			    end else begin
				 if s < symsize
				   then s := s + 1
				   else s := 1;
				 if s = olds then symfull := true;
			    end;
		       end else begin { FOUND UNUSED TABLE ENTRY }
			    if poolfit(pos,lim) then begin
				 { PUT THE SYMBOL IN THE POOL AND TABLE }
				 id := putpool(pos,lim);
				 lookup := s;
			    end else begin { NO ROOM IN POOL FOR SYM }
				 poolfull := true;
			    end;
			    s := olds { TERMINATE LOOP };
		       end { IF };
		  end { WITH };
	     until s = olds;
	end { LOOKUP };

	function oplookup( pos,lim: inbufptr ): opptr;
	{ FIND THE SYMBOL BETWEEN POS AND LIM ON THE CURRENT LINE IN
	   THE OPCODE TABLE, RETURN THE INDEX INTO THE TABLE WHERE IT
	   WAS FOUND OR SHOULD BE PUT; RETURN 0 IF IT ISN'T FOUND AND
	   THE TABLE IS FULL    				     }
	var s,olds:opptr;

	begin
	     s := hash(pos,lim,opcodes);
	     olds := s;
	     oplookup := 0 { DEFAULT RETURN VALUE };
	     repeat
		  with optab[s] do begin
		       if id<>0 then begin { HAVE NONBLANK ENTRY }
			    if poolcmp(id,pos,lim) then begin { FOUND IT }
				 oplookup := s;
				 s := olds { TERMINATE LOOP };
			    end else begin
				 if s < opcodes
				   then s := s + 1
				   else s := 1;
			    end;
		       end else begin { FOUND VACANCY }
			    oplookup := s;
			    s := olds { TERMINATE LOOP };
		       end;
		  end { WITH };
	     until s = olds;
	end { OPLOOKUP };


    { INSIDE SMAL.ONEPASS, UTILITY PARSING PROCEDURES }

	procedure getcomma;
	{ SKIP THE COMMA, COMPLAIN IF THERE ISN'T ONE }
	begin
	     if lex.typ = comma
	       then nextlex
	       else error(comexp,lex.pos,lex.lim);
	end { GETCOMMA };

	procedure skipbal;
	{ SKIP TO MACHING END PAREN WHEN GIVEN BEGIN PAREN }
	var nest:integer;
	    par:lexeme;
	begin
	     { ASSERT LEX.TYP = BPAR }
	     nest := 1;
	     par := lex;
	     repeat
		  nextlex;
		  if lex.typ = bpar
		    then nest := nest + 1
		    else if lex.typ = epar
			   then nest := nest - 1;
	     until (nest < 1) or (lex.typ = eol);
	     if lex.typ = eol then error(unbal,par.pos,par.lim);
	end { SKIPBAL };


    { INSIDE SMAL.ONEPASS, PROCEDURES TO PARSE EXPRESSIONS }

	procedure expression;
	{ PARSE EXPRESSIONS OF THE FORM
		<EXPRESSION> ::= <TERM> ! <EXPRESSION> <BINOP> <TERM>
	   RETURN THE VALUE OF THE EXPRESSION IN EXPR }
	var acc: value  	  { THE ACCUMULATOR };
	    accdef: boolean       { IS THE ACCUMULATOR DEFINED };
	    op: lexeme  	  { WHAT OPERATOR WAS FOUND };
	    expos: inbufptr       { POSITION OF START OF EXPRESSION };

	    procedure term;
	    { PARSE TERMS OF AN EXPRESSION OF THE FORM
		    <TERM> ::= [ <UNARY> ] <VALUE>
	       RETURN THE VALUE OF THE TERM IN EXPR }
	    var op:lexeme { UNARY OPERATOR };

		procedure value;
		{ PARSE VALUES OF AN EXPRESSION OF THE FORM
			<VALUE> ::= <IDENT> ! <NUM> ! . ! ( <EXPRESSION> )
				  ! <STRING> ! <IDENTIFIER> ( <ARGUMENT> )
		   RETURN THE VALUE OF THE VALUE IN EXPR }
		var symbol: symptr;
		    op: lexeme;
		    par: lexeme;
		begin
		     exprpos := lex.pos;
		     exprlim := lex.lim;
		     if lex.typ = num then begin  { GOT A NUMBER }
			  expr.offset := lex.val;
			  expr.base := abssym;
			  exprdef := true;
			  nextlex { READ OVER NUMBER };
		     end else if (lex.typ = quote) then begin { GOT STRING }
			  expr.base := 0;
			  exprdef := true;
			  expr.offset := lex.lim - lex.pos;
			  if expr.offset>4 then error(bounds,lex.pos,lex.lim);
			  if expr.offset = 3 then begin
			       expr.offset := ascii[ line[ lex.pos + 1 ] ];
			  end else if expr.offset >= 4 then begin
			       expr.offset := ascii[ line[ lex.pos + 2 ] ]
				    + ( 256 * ascii[ line[ lex.pos + 1 ] ] );
			  end else begin
			       expr.offset := 0;
			  end;
			  nextlex;
		     end else if (lex.typ = id)and(next.typ = bpar) then begin
			  op := lex;
			  nextlex { SKIP OPERATOR NAME };
			  par := lex;
			  nextlex { SKIP OPENING PAREN };
			  expr.base := abssym;
			  expr.offset := 1 { DEFAULT TO AMBIGUOUS };
			  exprdef := true  { DEFAULT TO DEFINED };
			  if poolcmp(funcdf,op.pos,op.lim) then begin
			       if lex.typ = id then begin
				    symbol := lookup(lex.pos,lex.lim);
			       end else begin
				    symbol := 0;
				    error(idexp,lex.pos,lex.lim);
			       end;
			       nextlex { SKIP OPERAND };
			       if symbol <> 0 then expr.offset
				 := -ord(setyet in symtab[symbol].use);
			  end else if poolcmp(funcfw,op.pos,op.lim)then begin
			       if lex.typ = id then begin
				    symbol := lookup(lex.pos,lex.lim);
			       end else begin
				    symbol := 0;
				    error(idexp,lex.pos,lex.lim);
			       end;
			       nextlex { SKIP OPERAND };
			       if symbol <> 0 then expr.offset
				 := -ord(   (usedyet in symtab[symbol].use)
				      and not(setyet in symtab[symbol].use));
			  end else if poolcmp(functy,op.pos,op.lim)then begin
			       expression;
			       expr.offset := expr.base;
			       expr.base := abssym;
			  end else if poolcmp(funcle,op.pos,op.lim)then begin
			       if lex.typ = epar then begin
				    expr.offset := 0;
			       end else begin
				    expr.offset := lex.pos;
				    if lex.typ = bpar then skipbal;
				    while not(next.typ in [eol,epar]) do begin
					 nextlex;
					 if lex.typ = bpar then skipbal;
				    end;
				    expr.offset := lex.lim - expr.offset;
				    nextlex;
			       end;
			  end else if poolcmp(funchi,op.pos,op.lim) then begin
			       { This block added by RZTM }
			       expression;
			       if lex.typ = epar then begin
				    if expr.base = abssym then begin
					 if expr.offset < 0 then begin
					    expr.offset := 128 + (((expr.offset
							 + 32767) + 1) div 256)
					 end else begin
					    expr.offset := expr.offset div 256;
					 end;
				    end else begin
					 error(badrel,exprpos,exprlim)
				    end;
				    exprpos := op.pos;
				    exprlim := lex.lim;
			       end else begin
				    error(unbal,par.pos,par.lim);
			       end;
			  end else if poolcmp(funclo,op.pos,op.lim) then begin
			       { This block added by RZTM }
			       expression;
			       if lex.typ = epar then begin
				    if expr.base = abssym then begin
					 if expr.offset < 0 then begin
					      expr.offset := ((expr.offset +
							   32767) + 1) mod 256;
					 end else begin
					    expr.offset := expr.offset mod 256;
					 end;
				    end else begin
					 error (badrel,exprpos,exprlim);
				    end;
				    exprpos := op.pos;
				    exprlim := lex.lim;
			       end else begin
				    error(unbal,par.pos,par.lim);
			       end;
			  end else begin
			       error(unfunc,op.pos,op.lim);
			       nextlex;
			  end;
			  if lex.typ = epar then begin
			       exprpos := op.pos;
			       exprlim := lex.lim;
			       nextlex { SKIP END PAREN };
			  end else begin
			       error(unbal,par.pos,par.lim);
			  end;
		     end else if lex.typ = id then begin  { GOT IDENTIFIER }
			  symbol := lookup(lex.pos,lex.lim);
			  if symbol > 0 then with symtab[symbol] do begin
			       use := use + [usedyet];
			       if (def in use) or (lab in use) then begin
				    expr := val;
				    exprdef := true;
			       end else begin
				    error(undef,lex.pos,lex.lim);
				    expr.offset := 0;
				    expr.base := abssym;
				    exprdef := false;
			       end;
			  end else begin
			       expr.offset := 0 { NO ERR ON FULL TABLE };
			       expr.base := abssym;
			       exprdef := true { PRETEND IT'S DEFINED };
			  end { IF };
			  nextlex { READ OVER IDENTIFIER };
		     end else if lex.typ = dot then begin
			  expr := loc;
			  exprdef := true;
			  nextlex { READ OVER DOT };
		     end else if lex.typ = bpar then begin
			  par := lex;
			  nextlex;
			  expression;
			  if lex.typ = epar then begin
			       exprpos := par.pos;
			       exprlim := lex.lim;
			       nextlex;
			  end else begin
			       error(unbal,par.pos,par.lim);
			  end;
		     end else begin   { GOT SOMETHING ELSE }
			  error(notval,lex.pos,lex.lim);
			  expr.offset := 0;
			  expr.base := abssym;
			  exprdef := false;
			  if not(lex.typ in [epar,eol,comma])
			    then nextlex { READ OVER WHATEVER IT IS };
		     end;
		end { VALUE };

	    begin { TERM }
		 if lex.typ in [plus,minus,notsym] then begin { UNARY }
		      op := lex;
		      nextlex { READ OVER UNARY OPERATOR };
		      value { GET VALUE TO BE MODIFIED };
		      exprpos := op.pos;
		      case op.typ of
		       plus:  ;
		       minus: if expr.base = abssym
				then expr.offset := neg(expr.offset)
				else error(badrel,op.pos,op.lim);
		       notsym:if expr.base = abssym
				then expr.offset := inot(expr.offset)
				else error(badrel,op.pos,op.lim);
		      end { CASE };
		 end else begin { NO UNARY OPERATOR }
		      value;
		 end;
	    end { TERM };

	begin { expression };
	     term { get leading term };
	     acc := expr;
	     accdef := exprdef;
	     expos := exprpos { save pos for error handlers };
	     while (lex.typ in [plus,minus,gt,lt,eq,andsym,orsym])
		do begin
		  op := lex;
		  nextlex { skip over operator };
		  if (op.typ = lex.typ) and (op.typ in [gt,lt]) then begin
		       { it is a shift operator: >> or << }
		       nextlex { skip over remainder of operator };
		       if op.typ = gt
			 then op.typ := epar
			 else op.typ := bpar;
		  end;
		  term { get following term };
		  if not(exprdef) then begin
		       accdef := false;
		  end else case op.typ of
		    plus: begin
			       acc.offset := add(acc.offset,expr.offset);
			       if acc.base = abssym then begin
				    acc.base := expr.base;
			       end else if expr.base <> abssym then begin
				    error(badrel,op.pos,op.lim);
				    acc.base := abssym;
			       end;
			  end { plus };
		   minus: begin
			       acc.offset := sub(acc.offset,expr.offset);
			       if acc.base = expr.base then begin
				    acc.base := abssym
			       end else if expr.base <> abssym then begin
				    error(badrel,op.pos,op.lim);
				    acc.base := abssym;
			       end;
			  end { minus };
		gt,lt,eq: if acc.base = expr.base then begin
			       case op.typ of
				 gt: acc.offset:=-ord(acc.offset>expr.offset);
				 lt: acc.offset:=-ord(acc.offset<expr.offset);
				 eq: acc.offset:=-ord(acc.offset=expr.offset);
			       end { case };
			       acc.base := abssym;
			  end else begin
			       error(badrel,op.pos,op.lim);
			       acc.base := abssym;
			       acc.offset := 1 { neither true nor false };
			  end { gt,lt,eq };
	    andsym,orsym: if (acc.base=abssym)and(expr.base=abssym) then begin
			       case op.typ of
			      andsym: acc.offset:=iand(acc.offset,expr.offset);
			       orsym: acc.offset:=ior(acc.offset,expr.offset);
			       end { case };
			  end else begin
			       error(badrel,op.pos,op.lim);
			  end { andsym,orsym };
	       bpar,epar: if (acc.base=abssym)and(expr.base=abssym) then begin
			       if expr.offset > 16 then expr.offset := 16;
			       while expr.offset > 0 do begin 
				     with acc do case op.typ of
			           bpar: offset:=add(offset,offset);
			           epar: if offset > 0
					   then offset := offset div 2
					   else offset :=
					      (((offset+32767)+1)div 2)+16384;
				     end;
				     expr.offset := expr.offset - 1;
			       end;
			  end else begin
			       error(badrel,op.pos,op.lim);
			  end { shift operators }
		  end { case };
	     end { while loop processing terms };
	     expr := acc;
	     exprdef := accdef;
	     exprpos := expos;
	end { expression };

	procedure expresbal;
	{ EVALUATE EXPRESSIONS, ASSURING BALANCED PARENS }
	begin
	     expression;
	     while lex.typ = epar do begin
		  error(unbal,lex.pos,lex.lim);
		  nextlex;
	     end;
	end { EXPRESBAL };

	procedure boundval(var val:integer; min,max:integer);
	{ BOUND CHECK THE EXPRESSION VALUE }
	begin
	     if (val < min) or (val > max) then begin
		  error(bounds,exprpos,exprlim);
		  val := min;
	     end;
	end { BOUNDVAL };

	function predicate: boolean;
	{ EVALUATE PREDICATES FOR IF AND ELSEIF DIRECTIVES }
	begin
	     expresbal { EVALUATE EXPRESSION };
	     predicate := false { DEFAULT };
	     if expr.base = abssym then begin
		  if expr.offset = -1
		    then predicate := true;
	     end else begin
		  error(badrel,exprpos,exprlim);
	     end;
	end { PREDICATE };


    { INSIDE SMAL.ONEPASS, PROCESSING OF KEY SYNTACTIC ELEMENTS }

	procedure labeldef;
	{ PARSE LABEL DEFINITION; DEFINE LABEL AND HANDLE MULTIPLES }
	var symbol: symptr;
	begin
	     { ASSUME THAT (LEX.TYP = ID) AND (NEXT.TYP = COLON) }
	     symbol := lookup( lex.pos, lex.lim );
	     if symbol > 0 then begin { THE SYMBOL IS IN THE TABLE }
		  with symtab[symbol] do begin
		       if (setyet in use) then begin
			    error(muldef,lex.pos,lex.lim);
		       end else if (lab in use) then begin
			    if (val.offset<>loc.offset)or(val.base<>loc.base)
			      then error(phase,lex.pos,lex.lim);
		       end else begin
			    val := loc;
		       end;
		       use := use + [lab,setyet];
		  end;
	     end;
	     nextlex { READ OVER ID };
	     nextlex { READ OVER COLON };
	end { LABELDEF };

	procedure definition;
	{ PARSE AND PROCESS DEFINITION OF FORM <ID> = <EXPRESSION> }
	var symbol: symptr;
	begin
	     symbol := lookup( lex.pos, lex.lim );
	     if lab in symtab[symbol].use then error(muldef,lex.pos,lex.lim);
	     nextlex { READ OVER ID };
	     nextlex { READ OVER EQ };
	     expresbal;
	     if symbol > 0 then with symtab[symbol] do begin
		  use := use + [setyet];
		  if exprdef then begin
		       use := use + [def];
		       val := expr;
		  end;
	     end;
	end { DEFINITION };

	procedure origin;
	{ PARSE AND PROCESS DEFINITIONS OF THE FORM . = <EXPRESSION> }
	begin
	     nextlex { SKIP DOT };
	     nextlex { SKIP EQ };
	     expresbal;
	     loc := expr;
	end { ORIGIN };

	procedure opcode;
	{ PARSE OPCODE FIELD, LOOKUP OPCODE, RETURN FORMAT INFORMATION
	   IN GLOBAL VARIABLES OPTYPE AND OPVAL 		       }
	var i:opptr;
	begin
	     { ASSUME THAT LEX.TYP = ID, SINCE OPCODE IS VALID IDENTIFIER }
	     oppos := lex.pos;
	     oplim := lex.lim;
	     i := oplookup(oppos,oplim);
	     if i <> 0 then if optab[i].id = 0 then i := 0;
	     if i = 0 then begin
		  optype := operr;
	     end else begin
		  optype := optab[i].typ;
		  opval := optab[i].val;
	     end;
	     nextlex { HAVING IDENTIFIED OPCODE, READ PAST IT };
	end { OPCODE };

	procedure getop;
	{ SKIP AND IGNORE LABELS ON A LINE, RETURN THE OPCODE GLOBALLY
	   SUPPRESS ANY ERROR MESSAGES ENCOUNTERED IN PARSING THE LINE }
	begin
	     startup;
	     while (lex.typ = id) and (next.typ = colon) do begin
		  nextlex { SKIP ID };
		  nextlex { SKIP COLON };
	     end;
	     if lex.typ = id then begin
		  if next.typ = eq
		    then optype := operr
		    else opcode;
	     end else optype := operr;
	     erset := [];
	end { GETOP };


    { INSIDE SMAL.ONEPASS, PROCESSING OF EXTERNAL SYMBOL LINKAGES }

	procedure internl;
	{ PARSE AND PROCESS INTERNAL SYMBOL DEFINITIONS }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then with symtab[symbol] do begin
		       use := use + [intdef];
		       if (use * [def,lab]) = []
			 then error(undef,lex.pos,lex.lim);
		  end { IF WITH };
	     end else begin
		  error(idexp,lex.pos,lex.lim);
	     end;
	     nextlex { READ OVER INTERNAL SYMBOL NAME };
	end { INTERNL };

	procedure makeext(symbol:symptr);
	{ MAKE OR VERIFY THAT THE CURRENT SYMBOL IS EXTERNAL }
			   { USED ONLY FROM EXTERNL AND COMDEF }
	begin
	     with symtab[symbol] do begin
		  if (setyet in use) then begin
		       error(muldef,lex.pos,lex.lim);
		  end else if (usedyet in use) then begin
		       error(fwdref,lex.pos,lex.lim);
		  end else if (lab in use) then begin
		       if (val.base <> id) or (val.offset <> 0)
			 then error(muldef,lex.pos,lex.lim);
		  end else begin { SYMBOL PREVIOUSLY UNUSED }
		       val.base := id;
		       val.offset := 0;
		  end;
		  use := use + [lab,setyet];
	     end { WITH };
	end { MAKEEXT };

	procedure externl;
	{ PARSE AND PROCESS EXTERNAL SYMBOL DECLARATIONS }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then makeext(symbol);
	     end else begin
		  error(idexp,lex.pos,lex.lim);
	     end;
	     nextlex { READ OVER EXTERNAL SYMBOL NAME };
	end { EXTERNL };

	procedure comdef;
	{ PARSE AND PROCESS COMMON DECLARATIONS }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then with symtab[symbol] do begin
		       makeext(symbol);
		       nextlex { READ OVER COMMON NAME };
		       getcomma;
		       expresbal { GET COMMON SIZE OR MAXIMUM LOCATION };
		       if (expr.base = abssym)
		       or (expr.base = id) then begin
			    if allowlist then begin
				 write(obj,'IF\DEF(S');
				   writesym(obj,id);
				     writeln(obj,')');
				 write(obj,' S');
				   writesym(obj,id);
				     write(obj,'=#');
				       writehex(obj,expr.offset,4);
					 writeln(obj);
				 writeln(obj,'ENDIF');
				 write(obj,'IF\DEF(R');
				   writesym(obj,id);
				     writeln(obj,')');
				 write(obj,' R');
				   writesym(obj,id);
				     writeln(obj,'=C');
				 write(obj,' C=C+S');
				   writesym(obj,id);
				     writeln(obj);
				 writeln(obj,' CT=.');
				 writeln(obj,' .=C');
				 writeln(obj,' .=CT');
				 writeln(obj,'ENDIF');
			    end;
		       end else begin
			    error(badrel,exprpos,exprlim);
		       end;
		  end else begin { SYMBOL TABLE FULL }
		       nextlex { SKIP OVER NAME };
		       getcomma;
		       expresbal { SKIP OVER SIZE };
		  end;
	     end else begin { COMMON NAME MISSING }
		  error(idexp,lex.pos,lex.lim);
	     end;
	end { COMDEF };


    { INSIDE SMAL.ONEPASS, PROCESSING OF TEXT INSERTIONS }

	procedure insert;
	{ process use directive (push one input file on stack) }
	var i:1..filelen;
	    pos:inbufptr;
	    startpos:1..filelen;
	begin
	     if lex.typ=quote then begin
		  if getlevel < maxgetl then begin
		       pushget { save current source };
		       gettext := 0 { set source to file, not macro };
		       actcnt := 0 { set to no macro parameters };
		       getlevel := getlevel + 1;
		       pos := lex.pos + 1;
		       startpos := 1;
		       if line[pos] <> pathbrk then begin { relative path }
			    infile[getlevel] := infile[getlevel - 1];
			    for i := 1 to filelen - 1
			      do if infile[getlevel][i] = pathbrk
				   then startpos := i + 1;
		       end;
		       for i := startpos to filelen do begin
			    if pos < (lex.lim - 1) then begin
				 infile[getlevel][i] := line[pos];
				 pos := pos + 1;
			    end else begin
				 infile[getlevel][i] := ' ';
			    end;
		       end;
		       case getlevel of
		       {1: reset(inp1,infile[1]); -- this is not possible}
			2: reset(inp2,infile[2]);
			3: reset(inp3,infile[3])
		       end;
		  end else begin
		       error(maxuse,lex.pos,lex.lim);
		  end;
	     end else begin
		  error(quoexp,lex.pos,lex.lim);
	     end;
	     nextlex { read over file name };
	end { insert };

	procedure macdef;
	{ PROCESS MACRO DEFINITIONS OF THE FORM:
	       MACRO <NAME> [ <PARAM> [ , <PARAM> ]* ] <BODY>          }
	var m:opptr;
	    parmtab: array [1..parmlim] of poolref;
	    parms: 0..parmlim;
	    oldsp: poolref;

	    procedure getpar;
	    { PARSE ONE FORMAL PARAMETER OF FORM:
		  <PARAM> := <ID>  !  ( <ID> )  !  = <ID>
	       CORRESPONDING TO BY NAME, BY LIST OF NAMES, AND BY VALUE }
	    var parm: lexeme { THE PARAMETER IDENTIFIER };
		par: lexeme  { THE POSITION OF THE BEGIN PAREN };
		typ: char    { THE TYPE OF THE FORMAL PARAMETER };
	    begin { GETPAR };
		 if parms < parmlim then begin
		      if lex.typ = id then begin { NAME PARAMETER }
			   parm := lex;
			   typ := 'A';
		      end else if lex.typ = eq then begin { VALUE PARAM }
			   nextlex;
			   if lex.typ = id then begin
				parm := lex;
				typ := '=';
			   end else begin
				parm.typ := eol;
				error(idexp,lex.pos,lex.lim);
			   end;
		      end else if lex.typ = bpar then begin { VALUE PARM }
			   par := lex { HOLD ONTO POSITION FOR ERRORS };
			   nextlex { SKIP OVER PAREN };
			   if lex.typ = id then begin
				parm := lex;
				typ := '(';
				nextlex { SKIP OVER IDENTIFIER };
				if lex.typ <> epar
				  then error(unbal,par.pos,par.lim);
			   end else begin
				parm.typ := eol;
				error(idexp,lex.pos,lex.lim);
			   end;
		      end else begin { BAD PARAMETER }
			   parm.typ := eol;
			   error(idexp,lex.pos,lex.lim);
		      end;
		      if parm.typ = id then begin { HAVE A GOOD PARAM }
			   parms := parms + 1;
			   if firstpass then begin
				parmtab[parms] := pushtext(parm.pos,parm.lim);
				putch(typ);
			   end;
		      end;
		 end else begin { TOO MANY PARAMETERS }
		      error(parovf,lex.pos,lex.lim);
		 end { PROCESSING ONE PARAMETER };
		 nextlex { READ OVER PARAMETER };
	    end { GETPAR };

	    procedure getbody;
	    { PARSE MACRO BODY OF FORM: <BODY> ::= <LINESEQUENCE> ENDMAC }
	    type parm=0..parmlim;
	    var nest:integer  { COUNTER TO FIND RIGHT ENDMAC WHEN NESTED };
		pos,lim:inbufptr  { PROGRESS POINTERS FOR PARAMETER SCAN };
		parmnum:parm  { IDENTITY OF CURRENT PARAMETER };

		function lookup(pos,lim:inbufptr):parm;
		{ LOOKUP CANDIDATE FORMAL PARAMETER NAME }
		var i:parm;
		begin
		     lookup := 0;
		     i := 0;
		     while i < parms do begin
			  i := i + 1;
			  if poolcmp(parmtab[i],pos,lim) then begin
			       lookup := i;
			       i := parms;
			  end;
		     end;
		end { LOOKUP };

	    begin { GETBODY }
		 nest := 1;
		 repeat
		      if listing then listline;
		      getop;
		      if optype = opmac
			then nest := nest + 1
			else if optype = opendm
			       then nest := nest - 1
			       else if optype = opend
				      then nest := 0;
		      if (nest > 0) and firstpass then begin { SAVE TEXT }
			   pos := 1;
			   while pos <= length do begin
				while not(line[pos] in letters)
				  and (pos <= length) do begin
				     if line[pos] = '''' then begin
					  pos := pos + 1;
					  { ASSERT LINE[LENGTH+1] = ';' }
					  while line[pos] = '''' do begin
					       putch('''');
					       pos := pos + 1;
					  end;
				     end else begin
					  putch(line[pos]);
					  pos := pos + 1;
				     end;
				end;
				if pos <= length then begin
				     lim := pos;
				     { LOWLETTERS and '_' added by RZTM }
				     while line[lim] in (letters + digits
					+ lowletters + ['_']) do begin
					{ Upshift IF added by RZTM }
					if line[lim] in lowletters then
					   line[lim] := chr(ord(line[lim]) -
					      (ord('a') - ord('A')));
					lim := lim + 1
				     end;
				     parmnum := lookup(pos,lim);
				     if parmnum > 0 then begin
					  putch(pooldel);
					  putch(chr(parmnum + ord('0')));
				     end else begin
					  for pos := pos to lim-1
					    do putch(line[pos]);
				     end;
				     pos := lim;
				end;
			   end { WHILE };
			   putch(pooldel);
			   putch(',');
		      end { ONE LINE OF TEXT WAS STORED };
		 until nest < 1;
		 poolsp := oldsp { POP FORMAL PARAMETER TABLE FROM STACK };
		 if optype = opend then begin { FOUND END OF FILE, NOT ENDM }
		      error(misemc,0,0);
		      popget;
		 end;
		 if firstpass then begin
		      putch(pooldel);
		      putch(pooldel) { TWO POOLDEL'S IN A ROW END A MACRO };
		 end;
	    end { GETBODY };

	begin { MACDEF }
	     parms := 0;
	     oldsp := poolsp { MARK STACK TOP, ALLOWING TEMPORARY USE };
	     if lex.typ = id then begin { HAVE MACRO NAME }
		  m := oplookup(lex.pos,lex.lim);
		  if m <= 0 then begin { NO ROOM IN TABLE }
		       opfull := true;
		  end else if firstpass then begin { DEFINE MACRO NAME }
		       if (optab[m].id=0) then begin { FIRST DEFINITION }
			    if poolfit(lex.pos,lex.lim) then begin
				 optab[m].id := putpool(lex.pos,lex.lim);
				 optab[m].typ := opmcall;
				 optab[m].val := poolpos + 1;
			    end;
		       end else begin { REDEFINITION }
			    optab[m].typ := opmcall;
			    optab[m].val := poolpos + 1;
		       end;
		  end;
		  nextlex { SKIP OVER MACRO NAME };
		  if lex.typ <> eol then begin
		       getpar;
		       while lex.typ <> eol do begin
			    getcomma;
			    getpar;
		       end;
		  end;
		  if firstpass then putch(pooldel) { MARK END OF PARMTYPES };
	     end else begin { MISSING MACRO NAME }
		  error(idexp,lex.pos,lex.lim);
		  nextlex { SKIP OVER JUNK };
	     end { PROCESSING MACRO HEADER };
	     if (lex.typ <> eol) and (erset = [])
	       then error(unproc,lex.pos,lex.lim);
	     getbody;
	end { MACDEF };

	procedure maccall( poolpos: poolref );
	{ CALL MACRO WHO'S TEXT IS STORED AT POOLPOS IN STRING POOL;
	   FORM OF CALL IS:
	   <NAME> [ <PARAM> [ , <PARAM> ]* ]    		  }

	    procedure getpar;
	    { PARSE A PARAMETER OF THE FORM:
	       <PARAM> ::= [ <LEXEME> ]*
			!  <EXPRESSION>
			!  ( [ <LEXEME> ]* ) [ : <EXPR> [ : <EXPR> ] ]  }
	    var typ:char { INDICATES EXPECTED PARAMETER TYPE };
		pos,lim:inbufptr { LOCATION OF PARAMETER };
		par:lexeme { POSITION INFO FOR BEGIN PAREN };
	    begin
		 typ := strpool[poolpos];
		 poolpos := poolpos + 1;
		 actcnt := actcnt + 1;
		 if lex.typ in [comma,eol] then begin { PARAMETER MISSING }
		      actparm[actcnt] := 0;
		 end else if typ = 'A' then begin
		      pos := lex.pos;
		      lim := lex.lim;
		      while not(lex.typ in [eol,comma]) do begin
			   if lex.typ = bpar
			     then skipbal
			     else if lex.typ = epar
				    then error(unbal,lex.pos,lex.lim);
			   lim := lex.lim;
			   nextlex;
		      end;
		      actparm[actcnt] := pushtext(pos,lim);
		 end else if typ = '=' then begin
		      expresbal;
		      if expr.base <> abssym then begin
			   actparm[actcnt] := pushtext(exprpos,exprlim);
		      end else begin
			   actparm[actcnt] := pushitxt(expr.offset);
		      end;
		 end else if typ = '(' then begin
		      if lex.typ = bpar then begin
			   par := lex;
			   nextlex { SKIP PAREN AT LIST HEAD };
			   pos := lex.pos;
			   lim := pos { DEFAULT FOR EMPTY STRING };
			   while not(lex.typ in [eol,epar]) do begin
				if lex.typ = bpar then skipbal;
				lim := lex.lim;
				nextlex;
			   end;
			   if lex.typ = eol
			     then error(unbal,par.pos,par.lim)
			     else nextlex;
			   if lex.typ = colon then begin { SUBSTRING }
				nextlex;
				if lex.typ <> colon then begin
				     expresbal { GET START };
				     if expr.base <> abssym
				       then error(badrel,exprpos,exprlim);
				     if expr.offset > 1 then begin
					  if expr.offset > (lim - pos)
					    then pos := lim
					    else pos := pos + expr.offset - 1;
				     end;
				end;
				if lex.typ = colon then begin
				     nextlex;
				     expresbal { GET LENGTH };
				     if expr.base <> abssym
				       then error(badrel,exprpos,exprlim);
				     if expr.offset < (lim - pos) then begin
					  if expr.offset < 1
					    then lim := pos
					    else lim := pos + expr.offset;
				     end;
				end;
			   end;
			   if pos >= lim
			     then actparm[actcnt] := 0
			     else actparm[actcnt] := pushtext(pos,lim);
		      end else begin
			   error(parexp,lex.pos,lex.lim);
			   nextlex;
		      end;
		 end;
	    end { GETPAR };

	begin { MACCALL }
	     pushget { SAVE PREVIOUS MACRO EXPANSION STATUS BLOCK };
	     actcnt := 0;
	     while (strpool[poolpos] <> pooldel) and (lex.typ <> eol) do begin
		  getpar;
		  if lex.typ <> eol then getcomma;
	     end;
	     if lex.typ <> eol then error (parovf,lex.pos,lex.lim);
	     while strpool[poolpos] <> pooldel do poolpos := poolpos + 1;
	     gettext := poolpos + 1 { SET IT TO READ MACRO TEXT FROM POOL };
	     if (erset <> []) or poolfull then popget { STOP BAD CALLS };
	end { MACCALL };


    { INSIDE SMAL.ONEPASS, PROCESSING OF CONDITIONAL DIRECTIVES }

	procedure findend;
	{ SKIP OVER LINES UNTIL A LINE WITH ENDIF OR END OPCODE FOUND }
	var nest:integer;
	begin
	     nest := 0;
	     repeat { READ AND CHECK FOLLOWING LINES }
		  if listing then listline { FIRST LIST PREVIOUS LINE };
		  getop;
		  if optype = opif
		    then nest := nest + 1
		    else if optype = opendif
			   then nest := nest - 1;
	     until (optype = opend) or (nest < 0);
	     if optype = opend then begin
		  error(miseif,0,0);
		  popget;
	     end;
	end { FINDEND };

	procedure findelse;
	{ SKIP LINES UNTIL ONE WITH AN ELSE, ELSEIF <TRUE>, OR END FOUND }
	begin
	     repeat { READ OVER THEN PARTS (ALLOWING MULTIPLE ELSEIF'S) }
		  if (lex.typ <> eol) and (erset = [])
		    then error(unproc,lex.pos,lex.lim);
		  repeat
		       if listing then listline { LIST LINE TO BE SKIPPED };
		       getop;
		       while (optype = opif) do begin;
			    findend;
			    if listing then listline { LIST END };
			    if optype=opend
			      then optype := opendif { DON'T COMPLAIN TWICE }
			      else getop;
		       end;
		  until optype in [opend,opendif,opelse,opelseif];
		  if (optype = opelseif) then begin
		       if predicate then optype := opelse;
		  end;
	     until optype in [opend,opendif,opelse];
	     if optype = opend then begin
		  error(miseif,0,0);
		  popget;
	     end;
	end { FINDELSE };

    { Inside SMAL.ONEPASS: Procedure to do the lexical analsis to
       determine the addresing modes. The routine PROSOP was written
       by Roger Z.T. Marty }

    procedure prosop;
    var opcol: 1..addrmode;
	save : inbufptr;
	index: (indx,indy,inda,junk);

	function zeropage(zpmode,absmode:integer):integer;
	   { Can the operand be placed onto the Zero Page? }
	begin
	   if (expr.offset > 255) or (expr.base <> abssym) or
	      (expr.offset < 0) or (exprdef = false) then
	      zeropage := absmode
	   else
	      if mnemtab[opval,zpmode] = ilop then
		 zeropage := absmode
	      else
		 zeropage := zpmode
	end;

	procedure xyanot;
	   { Is the index X, Y, A or something else (junk)? }
	begin
	   if (lex.lim - lex.pos) = 1 then
	      if line[lex.pos] = 'X' then
		 index := indx
	      else
		 if line[lex.pos] = 'Y' then
		    index := indy
		 else
		    if line[lex.pos] = 'A' then
		       index := inda
		    else
		       index := junk
	   else
	      index := junk
	end;

     begin
	save := lex.pos; { Save for possible error mesages }
	if lex.typ = bpar then begin
	   nextlex;
	   expression;
	   if lex.typ = comma then begin
	      { Indexed Indirect Instructions }
	      opcol := inx;
	      if (expr.offset > 255) or (expr.offset < -128) then
		 error(notzp,lex.pos,lex.lim);
	      if expr.base <> abssym then
		 error(badrel,exprpos,exprlim);
	      nextlex;
	      if lex.typ = id then begin
		 xyanot;
		 if index = indx then begin
		    nextlex;
		    if lex.typ = epar then begin
		       nextlex;
		       while lex.typ = epar do begin
			  error( unbal, lex.pos, lex.lim );
			  nextlex;
		       end;
		    end else begin
		       error( eprexp, lex.pos, lex.lim);
		    end;
		 end else begin
		    error (notind,lex.pos,lex.lim);
		 end
	      end else begin
		 error (noexis,save,lex.lim);
	      end
	   end else begin
	      if lex.typ = epar then begin
		 nextlex;
		 if lex.typ = comma then begin
		    { Indirect Indexed Instructions }
		    opcol := iny;
		    if (expr.offset>255) or (expr.offset<-128) then
		       error(notzp,exprpos,exprlim);
		    if expr.base <> abssym then
		       error(badrel,exprpos,exprlim);
		    nextlex;
		    if lex.typ = id then begin
		       xyanot;
		       if index <> indy then
			  error (noexis,save,lex.lim);
		       nextlex;
		    end else begin
		       error (noexis,save,lex.lim);
		    end;
		 end else begin
		    { Indirect Instructions }
		    opcol := ind;
		 end;
	      end else begin
		 error (eprexp,lex.pos,lex.lim);
		 opcol := ind;
	      end;
	   end;
	end else if lex.typ = poundsym then begin
	   { Immediate Instructions }
	   nextlex;
	   expresbal;
	   if expr.base <> abssym then
	      error (badrel,exprpos,exprlim);
	   boundval(expr.offset, -128, 255);
	   opcol := imm;
	end else if lex.typ <> eol then begin
	   opcol := zp; { Harmless start to prove it is not ac. }
	   if lex.typ = id then begin
	      xyanot;
	      if index = inda then begin
		 nextlex;
		 opcol := ac 
	      end
	   end;
	   if opcol <> ac then begin
	      expresbal;
	      if lex.typ = comma then begin
		 { Indexed Instructons }
		 nextlex;
		 if lex.typ = id then begin
		    xyanot;
		    case index of
		       indx : begin
				 opcol := zeropage(zpx,x);
			      end;
		       indy : begin
				 opcol := zeropage(zpy,y);
			      end;
		       inda : begin
				 opcol := zeropage(zpx,x);
				 error (notind,lex.pos,lex.lim)
			      end;
		       junk : begin
				 opcol := zeropage(zpx,x);
				 error (notind,lex.pos,lex.lim);
			      end;
		    end;
		    nextlex;
		 end else begin
		    opcol := zeropage(zpx,x);
		    error (notind,lex.pos,lex.lim);
		 end;
	      end else begin
		 if opcol <> imp then
		    opcol := zeropage(zp,abs);
	      end;
	   end
	end else begin
	   opcol := imp;
	end;

	{ Fetch the actual hex opcode }
	opval := mnemtab[opval,opcol];
	if opval = ilop then
	   error (iladdr,save,lex.lim);
	{ Print the opcode }
	putobj(1,opval,abssym);
	case opcol of
	{ Print the operand, if any. }
	   zp,zpx,zpy,rel,imm,inx,iny:
	      putobj(1,expr.offset,expr.base);
	   abs,x,y,ind: putobj(2,expr.offset,expr.base);
	   ac,imp:;
	end;
     end; { PROSOP }


    { INSIDE SMAL.ONEPASS }

    begin { ONEPASS }
	 { LETTERS changed Roger Z.T. Marty to eliminate possible
	    problems wrought by use of EBCDIC. LOWLETTERS added by
	    Roger Z.T. Marty }
	 letters := ['A'..'I'] + ['J'..'R'] + ['S'..'Z'];
	 lowletters := ['a'..'i'] + ['j'..'r'] + ['s'..'z'];
	 digits := ['0'..'9'];  { THESE FOUR OUGHT TO BE CONSTANTS }
	 hexdigits := ['A'..'F'] + digits;
	    { [,], and $ added to LEXPUNCT by Roger Z.T. Marty }
	 lexpunc := [':','.',',','=','>','<','+','-','\','&','!','(',
		     ')','#'];
	 quotemarks := ['''','"'];
	 { LOWLETTERS added by Roger Z.T. Marty }
	 valid := letters + lowletters + quotemarks + digits + lexpunc +
		  [' ',';','$','@','%'];

	 poolsp := poolsize;
	 gettext := 0;
	 getlevel := 0;
	 oldsp := 0;
	 actcnt := 0;
	 pushget { PUT A DUMMY LEVEL ON THE STACK TO ALLOW CLEAN END };
	 getlevel := 1 { SETUP FOR READING AT NORMAL SOURCE LEVEL };
	 listlevel := 1 { SETUP SO IT WILL LIST ONLY MAIN LEVEL SOURCE };
	 lineno := 0;
	 loc.offset := 0;
	 loc.base := relsym;
	 maxrel := 0;
	 objloc := loc;
	 clearuse { SETUP SYMBOL TABLE FOR PASS };
	 newpage  { start listing on a new page };

	 while getlevel >= 1 do begin
	      listing := (listlevel > 0) and (allowlist);
	      startup { SETUP FOR PROCESSING A LINE };

	      while (lex.typ = id) and (next.typ = colon) do labeldef;

	      { NOW KNOW THAT IF LEX.TYP = ID, THEN NEXT.TYP <> COLON }
	      if lex.typ = id then begin
		   if next.typ = eq then begin { PROCESS DEFINITIONS }
			definition;
		   end else begin
			opcode;
			case optype of { FIND OUT WHAT CLASS OF OPCODE }
			operr: error(baddir,oppos,oplim);
			       { Add optypes here. }
			       { OPREL and OPABS added by RZTM }
			oprel: begin { Relative Branch Instructions }
				  expresbal;
				  expr.offset := sub(expr.offset,
						    loc.offset + 2);
				  if expr.base <> loc.base then
				     error(badrel,exprpos,exprlim)
				  else boundval(expr.offset,-128,127);
				  opval := mnemtab[opval,rel];
				  putobj(1,opval,abssym);
				  putobj(1,expr.offset,abssym);
			       end;
			opabs: begin { All other 6502 opcodes }
				  prosop;
			       end;
			  opb: begin { byte }
				    expresbal;
				    boundval(expr.offset,-128,255);
				    putobj(1,expr.offset,expr.base);
				    while lex.typ = comma do begin
					 nextlex;
					 expresbal;
					 boundval(expr.offset,-128,255);
					 putobj(1,expr.offset,expr.base);
				    end;
			       end;
			  opw: begin { word }
				    expresbal;
				    putobj(2,expr.offset,expr.base);
				    while lex.typ = comma do begin
					 nextlex;
					 expresbal;
					 putobj(2,expr.offset,expr.base);
				    end;
			       end;
		      opascii: begin { ascii text constant };
				    if lex.typ <> quote
				      then error(quoexp,lex.pos,lex.lim)
				      else putascii(lex.pos+1,lex.lim-1);
				    nextlex;
				    while lex.typ = comma do begin
					 nextlex;
					 if lex.typ = quote then begin
					      putascii(lex.pos+1,lex.lim-1);
					      nextlex;
					 end else begin
					      expresbal;
					      boundval(expr.offset,-128,255);
					      putobj(1,expr.offset,expr.base);
					 end;
				    end;
			       end;
			 opif: if not(predicate) then findelse;
	     opelse, opelseif: findend;
		      opendif:;
			opint: begin { internal definition }
				    internl;
				    while lex.typ = comma do begin
					 nextlex;
					 internl;
				    end;
			       end;
			opext: begin { external definition }
				    externl;
				    while lex.typ = comma do begin
					 nextlex;
					 externl;
				    end;
			       end;
		      opcomon: comdef { common definition };
			opmac: macdef  { process macro definition };
		       opendm: error(baddir,oppos,oplim);
			opuse: insert  { insert text from alt file };
		       oplist: begin { control listing }
				    expresbal;
				    if expr.base <> abssym then begin
					 error(badrel,exprpos,exprlim);
				    end else begin
					 listlevel := listlevel + expr.offset;
					 if (expr.offset < 0) and (erset = [])
					   then listing := (listlevel > 0)
							and (allowlist);
				    end;
			       end;
			opttl: begin { title directive }
				    settitle( titlebuf, titlelen,
					      lex.pos, length    );
				    lex.typ := eol;
			       end;
		      opsbttl: begin
				    if firstpass then begin
					 listline;
				    end else if listing then begin
					 settitle( sbttlbuf, sbttllen,
						   lex.pos, length    );
					 newpage;
					 lex.typ := eol;
				    end;
			       end;
		      opeject: if listing then lineonpg := linesper - 1;
			opend: popget;
		      opmcall: maccall(opval) { call the indicated macro };
			end { CASE OPTYPE FOR OPCODE CLASSES };
		   end { IF };
	      end else if (lex.typ = dot) and (next.typ = eq) then begin
		   origin;
	      end else if lex.typ <> eol then begin
		   error(baddir,lex.pos,lex.lim);
		   nextlex { SKIP OVER JUNK TO AVOID COMPLAINING TWICE };
	      end;
	      if (lex.typ <> eol) and (erset = [])
		then error(unproc,lex.pos,lex.lim);
	      if listing then listline;
	      if loc.base = relsym
		then if loc.offset > maxrel
		       then maxrel := loc.offset;
	 end { WHILE };
	 if allowlist then begin { MAKE SURE OBJECT CODE ENDS AT MAXREL }
	      if (loc.base <> relsym) or (loc.offset < maxrel) then begin
		   write(obj,'.=');
		   genval(2,maxrel,relsym);
	      end;
	 end;
    end { ONEPASS };


{ INSIDE SMAL, PROCEDURES TO DO FILE SETUP AND TAKEDOWN }

    procedure getfiles;
    {  read file name from terminal, store it in global "infile[1]"
	suffix it with ".obj" and store it in globals "objfile"
	suffix it with ".lst" and store it in global "lstfile"
	setup listing title to default to input file name       }
    var i : 1..filelen;
	j : 1..filelen;
	dot : 0..filelen;
	ch : char;
    begin
	 write('  INPUT FILE NAME: ');
	 { readln needed here in hull r-mode }
	 i := 1;
	 dot := 0;
	 while not(eoln(input)) and (i<=(filelen-4)) do begin
	      read(ch);
	      infile[1][i]:=ch;
	      if ch = '.' then dot := i;
	      i := i+1;
	 end;
	 if dot = 0 then dot := i;
	 for j := i to filelen do infile[1][j]:= ' ';
	 lstfile := infile[1];
	 for j := dot to i do lstfile[i] := ' ';
	 objfile := lstfile;
	 lstfile[dot] := '.';
	 objfile[dot] := '.';
	 lstfile[dot+1] := 'l';
	 objfile[dot+1] := 'o';
	 lstfile[dot+2] := 's';
	 objfile[dot+2] := 'b';
	 lstfile[dot+3] := 't';
	 objfile[dot+3] := 'j';

	 { setup default title and subtitle }
	 for j := 1 to i do titlebuf[j] := infile[1][j];
	 titlelen := i;
	 sbttllen := 0;
    end { getfiles };


{ INSIDE SMAL }

begin { SMAL6502 }
     { TEST IMPLEMENTATION CHARACTERISTICS }
     if maxint < tohex('7FFF') then writeln('*** INTEGERS TOO SMALL ***');
     if (-32767-1)>0 then writeln('*** MINUS NUMBERS TOO SMALL ***');
     { ASSUME THAT OVERFLOW WILL BE DETECTED }

     initascii;
     getfiles;
     reset(inp1,infile[1]);
     rewrite(output,lstfile);
     rewrite(obj,objfile);
     clearsym;
     opinit;
     onepass( { FIRSTPASS } true, { ALLOWLIST } false );
     reset(inp1,infile[1]);
     writeln(obj,'R=.');
     onepass( { FIRSTPASS } false, { ALLOWLIST } true );
     objsufx;
     if symfull then writeln('** SYMBOL TABLE OVERFLOWED **');
     if poolfull then writeln('** STRING POOL OVERFLOWED **');
     if opfull then writeln('** MACRO NAME TABLE FULL **');
end { SMAL6502 }.
