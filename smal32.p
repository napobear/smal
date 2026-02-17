{ smal32.p 
   language: Pascal
   copyright 1988 by Douglas W. Jones
		     University of Iowa
		     Iowa City, Iowa  52242
		     USA

   Permission is granted to make copies of this program for any purpose,
   provided that the above copyright notice is preserved in the copy, and
   provided that the copy is not made for direct commercial advantage.

   Note: This software was developed with no outside funding.  If you find
   it useful, and especially if you find it useful in a profit making
   environment, please consider making a contribution to the University
   of Iowa Department of Computer Science in care of:

		     The University of Iowa Foundation
		     Alumni Center
		     University of Iowa
		     Iowa City, Iowa  52242
		     USA
}
   
program smal32(input,output,o,obj,inp1,inp2,inp3); {$ D- }
      { Simple macro assembler and linkage editor with a 32 bit word.
	Started by D. W. Jones in the fall 1980 at the University of Iowa.
	rev 4/20/82 includes complete macro and conditional support.
	rev 5/5/82 includes errata and extensions.
	rev 2/5/84 yields 32-bit math, hex conversion.
	rev 12/1/88 to remove NS32000 specific code and run on Berkeley Pascal.
      }

      { as modified by E. Wedel, requires 32-bit integers, but only
	where explicitly called for by "oversized" subrange types.
	Will now cope 32 bit "words."  At present, only
	"oversized" subrange is the global type -longint-.            }

      { Originally coded in Hull r-mode Pascal for Prime computers:
	  this uses 16 bit integer representations and the char type has
	  only 64 elements.
	Works compatably in Hull v-mode Pascal for Prime computers:
	  this uses 32 bit integer representations and the char type uses
	  ASCII codes with the high bit always set to zero.
	Works in Prime Pascal (v-mode) when keyword 'packed' is deleted:
	  this uses 32 bit integer representations and the char type uses
	  ASCII codes with the high bit always set to one.
	Works in Berkeley Pascal, after date and time inquiry formats were
	  changed from Hull v-mode to make this work.
      }

      { As currently configured, this program must be run interactively;
	when run, it will request a file name from the terminal.  It
	will then assemble that file, placing the listing on a file
	named the same, but with an .l suffix.  Object code is generated
	similarly on a file with a .o suffix.   		     }

      { This assembler is written assuming that it will run on a
	machine with at least 32 bit two's complement integers.   }

const symsize = 300  { number of symbols allowed in symboltable };
      opcodes = 200  { opcodes and macro names allowed in optab };
      poolsize = 4000{ chars in stringpool; should be greater than the
			average symbol length times symsize, plus the
			average opcode or macro name length times opcodes,
			plus additional space for macro text storage,
			plus additional space for the macro call stack,
			at a minimum of 8 characters per macro nesting
			level, if no parameters are passed. 
			note: poolsize must not be increased above 32767
			unless appropriate changes are made to pushint and
			popint  					};
      relsym = 1   { offset of null symbol in pool };
      abssym = 0   { offset for abs symbol (just below pool };
      pooldel = '' { pool delimiter, an illegal character in programs,
		       presently set to control-A };
      pdelrep = '~' { replacement for virgin occurrences of -pooldel-
		       in input stream (ha!) } ;
      maxgetl = 3   { number of files in input file stack
		       changes to this require changing the number of files
		       in the input stack (inp1, inp2, and inp3) and changing
		       all case statements which select among these };
      parmlim = 8   { number of macro parameters per call.
		       note: increasing this above 9 will require changes
		       to onepass.getline.getmac and to onepass.macdef.getbody;
		       these currently use decimal digits to encode parameter
		       numbers, and must be changed to use some other scheme};
      linelen = 81  { one more than length of allowed input line };
      listcol = 20  { last column of listing used for object code info, should
		       set it so that: (listcol + linelen + 7)<(page width).
		       note that if listcol is changed to be less than 20, the
		       error messages must all be shortened to keep the error
		       markup under the right places on the input line.     };
      listcodes = 50{ object code items (bytes,words) listed on a line, set so
		       that: ((4       * listcodes) + 14) > listcol };
      ttlbuflen = 74{ field-size allocated to title and sub-title texts };
      linesper = 56 { lines per page on the listing device };
      filelen = 40  { characters per textual file name };
      pathbrk = '/' { break character in file system path names.  used for
		       implementation of USE in hierarchic file systems.
		       it is assumed in procedure insert that path names
		       starting with pathbrk are absolute, while those starting
		       with other characters are relative };

      maxposint = 2147483647; { max 32-bit signed positive value 2^31-1}
      maxposintdiv10 = 214748364; { maxposint DIV 10 (truncated) }
      maxposbit = 1073741824; { max negative int (abs) DIV 2 = 2^30}

type
     symptr = 0..symsize;
     opptr = 0..opcodes;

     { file name management types }
     filename = packed array [1..filelen] of char;

     { input line buffer types }
     linebuf = packed array [1..linelen] of char;
     inbufptr = 0..linelen;

     { listing prettifier buffer types }
     timetype = packed array[1..8] of char;
     datetype = packed array[1..16] of char;

     { extended (32-bit) arithmetic type }
     longint = integer; { HullV is 32-bit always.. }

     { symboltable types }
     poolref = 0..poolsize { reference to a location in the string pool };
     value = record
		  base:poolref { symbol from which offset is relocated };
		  offset:longint { offset from that symbol };
	     end;
     association = record
		      { fields known only to lookup routine }
		      id: poolref;

		      { fields known only by table users }
		      val: value;
		      use: set of (def,lab { is it a label or defined value }
				  ,intdef  { is the value to be exported }
				  ,usedyet { has value been used this pass }
				  ,setyet  { has value been set this pass }
				  );
		   end { record };

     { opcode types }
     optypes = (operr  { error }

	       { assembler directives }
	       ,opd    { double-word (32 bit) constant }
	       ,opif   { conditional assembly }
	       ,opelseif
	       ,opelse
	       ,opendif
	       ,opint  { internal symbol definition }
	       ,opext  { external symbol declaration }
	       ,opcomon{ common declaration }
	       ,opmac  { macro declaration }
	       ,opendm
	       ,opuse  { use text from secondary source }
	       ,oplist { listing control directive }
	       ,opttl  { title directive }
	       ,opsbttl{ subtitle directive }
	       ,opeject{ page eject directive }
	       ,opstart{ starting address specification }
	       ,opend  { end of file }

	       { macro call type }
	       ,opmcall{ macro call }

	       { add machine instruction types here }
	       );

var
    { the following constant is used for representation independant
       character code translation, it can be replaced with the ord function
       on some ascii implementations of pascal  			  }
    ascii: array [char] of 0..127;

    { all textual information stored by the assembler is in the string pool }
    strpool: packed array [relsym..poolsize] of char;

    { two data structures share the string pool: permanent text grows up
       from relsym, the last used location is pointed to by     	     }
    poolpos: poolref;

    { transient text grows down from poolsize, organized as a stack.  the
       format of each stack entry is documented in onepass.pushget           }

    { when the stringpool fills up, it is indicated by: 		    }
    poolfull: boolean;

    { some key-words are stored in the pool but not in any symbol table;
       these are pointed to by the following (constant) variables            }
    funcdf,funcfw,functy,funcle: poolref { function names };

    { the assembler symbol table for labels etc }
    symtab: array [1..symsize] of association;
    symfull: boolean { flag indicating symbol table is full };

    { the assembler symbol table for opcodes, directives, and macro names }
    optab: array [1..opcodes] of record
				    id:poolref;
				    typ:optypes;
				    val:integer;
				    subtyp:integer
				 end { record };
    opfull: boolean { flag indicating opcode table is full };

    { textual names of input and output files }
    outfile, objfile: filename;
    infile: array [1..maxgetl] of filename;
    inp1,inp2,inp3: text { shallow stack of source files };
    o: text { listing output file };
    obj: text { object code file };

    { title and subtitle buffers for listing }
    titlebuf,sbttlbuf: linebuf;
    titlelen,sbttllen: inbufptr;
    lineonpg: integer { used to determine when to print title };
    pagenum: integer { current page in assembly listing };
    errorcount: integer { global, set in -onepass-' routines };

    { date and time buffers for listing }
    datestr: datetype;
    timestr: timetype;


{ inside smal32, system date/time access routines..  }

{ Primos procedures to do the job
    procedure timeSa/time$a(var time: timetype addparity );
	 extern;

    procedure dateSa/date$a(var date: datetype addparity );
	 extern;
}

    procedure getdatetime;
    { fill datestr with "Mon. Jan. 1 '00", timestr with "12:00:00" }

    { Berkeley Pascal variables }
    var thedate, thetime: alfa;
    {}

    begin
	 { code for Primos
	 timeSa(time);
	 dateSa(date);
	 datestr[2] := chr(ord(datestr[2])-ord('A')+ord('a'));
	 datestr[3] := chr(ord(datestr[3])-ord('A')+ord('a'));
	 datestr[7] := chr(ord(datestr[7])-ord('A')+ord('a'));
	 datestr[8] := chr(ord(datestr[8])-ord('A')+ord('a'));
	 }

	 { code for Berkeley Pascal (doesn't give day of week, use ....) }
	 date(thedate);
	 time(thetime);
	 datestr := '.... 678. 12 ''56';
	 datestr[6] := thedate[4];
	 datestr[7] := thedate[5];
	 datestr[8] := thedate[6];
	 datestr[11] := thedate[1];
	 datestr[12] := thedate[2];
	 datestr[15] := thedate[8];
	 datestr[16] := thedate[9];
	 timestr := '12:45:67';
	 timestr[1] := thetime[2];
	 timestr[2] := thetime[3];
	 timestr[4] := thetime[5];
	 timestr[5] := thetime[6];
	 timestr[7] := thetime[8];
	 timestr[8] := thetime[9];
	 {}
    end { getdatetime };


{ inside smal32, procedure to initialize ascii translation array }

    procedure initascii;
    type string = packed array[1..16] of char;
	procedure initrow(row:integer;text:string);
	var i:1..16;
	begin
	     for i := 1 to 16 do ascii[text[i]] := (row * 16) + i - 1;
	end;
    begin
	 initrow(2,' !"#$%&''()*+,-./');
	 initrow(3,'0123456789:;<=>?');
	 initrow(4,'@ABCDEFGHIJKLMNO');
	 initrow(5,'PQRSTUVWXYZ[\]^_');
	 { on machines with a smaller character set, may omit rows 6 and 7 }
	 initrow(6,'`abcdefghijklmno');
	 initrow(7,'pqrstuvwxyz{|}~');
    end { initascii };


{ inside smal32, functions simulating 32 bit two's complement machine 
		 for efficiency, all of these may be re-implemented 
		 as external assembly language routines 	     }

    function add(i,j:longint):longint;
    begin
	 if (i > 0) and (j > 0) then begin
	      if i <= (maxposint - j)
		   then add := i + j
		   else add := ((i-maxposint)-1) + ((j-maxposint)-1);
	 end else if (i < 0) and (j < 0) then begin
	      if i >= (((-maxposint)-1)-j)
		   then add := i + j
		   else add := ((i+maxposint)+1) + ((j+maxposint)+1);
	 end else add := i + j;
    end { add };

    function neg(i:longint):longint;
    begin
	 if i = ((-maxposint)-1)
	   then neg := ((-maxposint)-1)
	   else neg := -i;
    end { neg };

    function sub(i,j:longint):longint;
    begin
	 sub := add(i,neg(j));
    end { sub };

    function ugt(i,j:longint):boolean;
    { unsigned greater than }
    begin
	 if i>=0 then begin
	      if j>=0
		then ugt := i>j
		else ugt := false;
	 end else begin { i<0 }
	      if j<0
		then ugt := i>j
		else ugt := true;
	 end;
    end { ugt };

    function mod10(i:longint):longint;
    begin
	 if i >= 0
	   then mod10 := i mod 10
	   else mod10 := (((i + maxposint + 1) mod 10) + 8) mod 10;
    end { mod10 };

    function div10(i:longint):longint;
    begin
	 if i >= 0
	   then div10 := i div 10
	   else div10 := ((i + maxposint + 1) div 10) + maxposintdiv10
		       + ((mod10(i + maxposint + 1) + 8) div 10);
    end { div10 };

    function inot(i:longint):longint;
    begin
	 inot := add(neg(i),-1);
    end { inot };

    function iand(i,j:longint):longint;
    var k,l:longint;
    begin
	 if (i<0) and (j<0) then k:=(-maxposint)-1 else k:=0;
	 if (i<0) then i := i + maxposint + 1;
	 if (j<0) then j := j + maxposint + 1;
	 if odd(i) and odd(j) then k := k + 1;
	 l := 1;
	 while l<maxposbit do begin
	      i := i div 2;
	      j := j div 2;
	      l := l  *  2;
	      if odd(i) and odd(j) then k := k + l;
	 end;
	 iand := k;
    end { iand };

    function ior(i,j:longint):longint;
    begin
	 ior := inot(iand( inot(i) , inot(j) ));
    end { ior };

    function rightshift(i:longint):longint;
    begin
	 if i > 0
	   then rightshift := i div 2
	   else rightshift := (((i + maxposint) + 1) div 2) + maxposbit;
    end { rightshift };


{ inside smal32, procedures for doing output format conversion }

    procedure writehex( var f:text; v:longint; l:integer);
    { write v as an l digit hex number on file f }
    var digits: array[1..8] of char;
	digit:  0..15;
	i:      integer;
    begin
	 if l > 8 then begin
	      for i:=l-1 downto 8 do
		   write(f, ' ');
	      l := 8
	 end;
	 for i := 1 to l do begin
	      if v < 0 then begin
		   v := v + maxposint + 1;
		   digit := v mod 16;
		   v := (v div 16) + 134217728
	      end else begin
		   digit := v mod 16;
		   v := v div 16;
	      end;
	      if digit < 10
		then digits[i] := chr(digit + ord('0'))
		else digits[i] := chr((digit - 10) + ord('A'));
	 end;
	 for i := l downto 1 do write(f,digits[i]);
    end { writehex };

    procedure writesym(var f:text; pos:poolref);
    { write the symbol from the symboltable on the indicated file }
    begin
	 while strpool[pos] <> pooldel do begin
	      write(f,strpool[pos]);
	      pos := pos + 1;
	 end;
    end { writesym };

    procedure genval( siz: integer; offset: longint;
		      base: poolref );
    { generate value in object file based on indicated
       symbol with the given offset from that symbol }
    begin
	 if base = abssym then begin
	      write(obj,'#');
	      writehex(obj,offset,2*siz);
	 end else begin
	      if offset = 0 then begin
		   write(obj,' ');
	      end else begin
		   write(obj,'#');
		   writehex(obj,offset,2*siz);
		   write(obj,'+');
	      end;
	      write(obj,'R');
	      writesym(obj,base);
	 end;
	 writeln(obj);
    end { genval };


{ inside smal32, procedures for symbol table management }

    procedure clearsym;
    { initialize all entries in the symbol table to unused }
    var i: symptr;
    begin
	 symfull := false;
	 for i := 1 to symsize do with symtab[i] do begin
	      id := 0;
	      use := [];
	 end;
    end { clearsym };

    procedure clearuse;
    { clear symbol table flags in preparation for one pass }
    var sym:symptr;
    begin
	 for sym := 1 to symsize do with symtab[sym] do begin
	      use := use - [usedyet,setyet];
	 end;
    end { clearuse };

    procedure objsufx;
    { generate suffix to object file which defines all internal symbols }
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
    end { objsufx };

    procedure opinit;
    { initialize the opcode table and string pool (done only once) }
    type string = packed array [1..8] of char;
    var i: integer;

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
	end { putpool };

	function hash(s:string; modulus:integer) : integer;
	{ it is critical that this hash function match that inside onepass }
	var i:1..8;
	    acc:integer;
	begin
	     acc := 1;
	     for i := 1 to 8 do if s[i]<>' '
	       then acc := (((acc*5) + ord(s[i])) mod modulus) + 1;
	     hash := acc;
	end { hash };

	procedure op(s:string; t:optypes; v:integer);
	begin
	     i := hash(s, opcodes);
	     while optab[i].id <> 0 do i := (i mod opcodes) + 1;
	     optab[i].id := putpool(s);
	     optab[i].typ := t;
	     optab[i].val := v;
	     optab[i].subtyp := 0
	end { op };


    begin { opinit };
	 getdatetime;
	 pagenum := 0; { set multi-pass page number }

	 for i := 1 to opcodes do optab[i].id := 0;
	 poolfull := false;
	 opfull := false;
	 poolpos := relsym;
	 strpool[poolpos] := pooldel;
	 { null symbol at start of pool is default relocation base }
	 op('W       ',opd      ,0);
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
	 op('S       ',opstart  ,0);
	 op('END     ',opend    ,0);
	{ note: when adding to this list, be sure to adjust the constant
	    'opcodes' to reflect the additions; the local procedure
	    'op' used above assumes that the opcode table will always
	    have some free space.       			      }

	{ following establish unary function names.. }
	 funcdf := putpool('DEF     ');
	 funcfw := putpool('FWD     ');
	 functy := putpool('TYP     ');
	 funcle := putpool('LEN     ');

    end{ opinit };

{ inside smal32, main assembly procedure for one pass through source }

    procedure onepass( firstpass,allowlist: boolean );
    {  perform one assembly pass.  produce output if listing=true  }

    type ermsg = (minermsg
		 ,baddig { bad digit in number }
		 ,baddir { bad assembly directive }
		 ,badrad { bad radix }
		 ,badrel { misuse of relocation in expression }
		 ,bounds { value out of bounds }
		 ,comexp { comma expected }
		 ,fwdref { definition must precede use }
		 ,idexp  { identifier expected }
		 ,maxuse { too many source files }
		 ,miseif { missing endif }
		 ,misemc { missing endmac }
		 ,misquo { missing end quote }
		 ,muldef { multiple symbol definition }
		 ,mulstt { multiple start directives }
		 ,notfit { text too long for line }
		 ,notlab { expected label or directive }
		 ,notval { expected a value, got something else }
		 ,parexp { parenthesized list expected }
		 ,parovf { too many macro parameters }
		 ,phase  { phase error in label value between passes }
		 ,quoexp { quoted string expected }
		 ,unbal  { unbalanced parens }
		 ,undef  { undefined symbol }
		 ,unfunc { bad function }
		 ,unproc { unprocessed data at end of line }

		 ,maxermsg);

	 { types having to do with lexical analysis }
	 lextypes = (id       { identifier }
		    ,num      { number (hex or decimal) }
		    ,quote    { quoted string }
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
		    ,eol      { end of line and start of comment }
		    ,junk     { string of unclassified characters }
		    );
	 lexeme = record
		       pos,lim: inbufptr { start, end of lexeme in line };
		       case typ: lextypes of
			num: ( val: longint { value of number }        )
		  end {record};

    var letters, upperc, digits, hexdigits,
	quotemarks, lexpunc, valid:   set of char;
       { the above are supposed to be constants }

	loc: value      { current assembly location counter };
	maxrel: integer { max val of loc.offset when loc.base = relsym };
	startloc: value { starting address, if specified };
	objloc: value   { current object code generation location counter };
	lineno: integer { current line in assembly source };

	lex: lexeme     { current lexeme };
	next: lexeme    { next lexeme for lookahead use };

	{ variables associated with stack on transient end of stringpool }
	poolsp: poolref       { pool stack pointer };
	oldsp:  poolref       { pointer to previous frame in stack };
	actcnt: 0..parmlim    { count of actual params in current frame };
	actparm: array [1..parmlim] of poolref { pointers to ap's in frame };

	{ variables controlling source of input }
	gettext: poolref      { loc in pool from which macro text comes };
	getlevel: 0..maxgetl  { file from which non-macro text comes };

	{ line buffers and lexical analysis }
	line: linebuf;
	pos: 1..linelen 	{ current input line position };
	length: inbufptr	{ current input line length };

	{ record of errors on the current line }
	erbuf: linebuf        { markup under error };
	ermax: inbufptr       { max used position in erbuf };
	erset: set of ermsg   { set of messages to generate };
	seenstart: boolean    { detects multiple start dirs };

	{ record of code generated by current line }
	codebuf: array [1..listcodes] of record
				      val: value;
				      form: 1..1;
				 end;
	codelen: 0..listcodes;
	codeloc: value;

	{ listing control variables }
	listing: boolean  { set to (listlevel > 0) and (allowlist) };
	listlevel: integer { dec on macro call, inc on return };

	{ info about last expression }
	expr:value            { value of expression };
	exprdef:boolean 	 { is the value of the expression defined };
	exprundef:boolean;     { does expr. contain fwd ref(s)? }
	exprpos,exprlim:inbufptr { position of expression on line };

	{ info about opcode decoded on current line }
	optype:optypes;
	opval:integer;
	opsubt:integer;
	oppos,oplim:inbufptr;


    { inside smal32.onepass, routines to manage stack in stringpool,
		     these routines assume that ord(maxch)>=32; if
		     ord(maxch)>32, they may be recoded for greater
		     efficiency without any effect on their users   }

	procedure pushchar(ch:char);
	{ push one char onto stack in stringpool }
	begin
	     if poolsp > poolpos then begin
		  strpool[poolsp] := ch;
		  poolsp := poolsp - 1;
	     end else begin
		  poolfull := true;
	     end;
	end { pushchar };

	function pushtext(pos,lim:inbufptr):poolref;
	{ push the indicated text onto the stack from the line,
	   as a terminated string, return a reference to the first char }
	var i:inbufptr;
	begin
	     pushchar(pooldel);
	     for i := lim-1 downto pos do pushchar(line[i]);
	     pushtext := poolsp + 1;
	end { pushtext };

	function pushitxt(i:integer):poolref;
	{ push the indicated integer as a decimal text string, terminated
	   with a pooldel, and return a reference to the first char }
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
	end { pushitxt };

	function popchar:char;
	{ pop one char from stack in stringpool }
	begin
	     poolsp := poolsp + 1;
	     popchar := strpool[poolsp];
	end { popchar };

	procedure pushint(i:integer);
	{ push an integer onto stack as a sequence of chars }
	begin
	     pushchar(chr( i mod 32 ));
	     pushchar(chr( (i div 32) mod 32 ));
	     pushchar(chr( i div 1024 ));
	end { pushint };

	function popint:integer;
	{ pop an integer from the stack as a sequence of chars }
	var i:integer;
	begin
	     i := ord(popchar) * 1024;
	     i := i + (ord(popchar) * 32);
	     popint := i + ord(popchar);
	end { popint };

	procedure pushget;
	{ push a macro expansion control block on the stack }
	var i:1..parmlim;
	begin
	     listlevel := listlevel - 1;
	     for i := 1 to actcnt do pushint(actparm[i]);
	     pushchar(chr(actcnt));
	     pushint(oldsp);
	     pushint(gettext);
	     pushchar(chr(getlevel));
	     oldsp := poolsp;
	end { pushget };

	procedure popget;
	{ pop a macro expansion control block from the stack }
	var i:1..parmlim;
	begin
	     if poolfull then begin { can't pop safely, so go all the way }
		  listlevel := 1;
		  gettext := 0;
		  getlevel := 0;
	     end else begin { can pop one level safely }
		  listlevel := listlevel + 1;
		  poolsp := oldsp;
		  getlevel := ord(popchar);
		  gettext := popint;
		  oldsp := popint;
		  actcnt := ord(popchar);
		  for i := actcnt downto 1 do actparm[i] := popint;
	     end;
	end { popget };


    { inside smal32.onepass, input/output routines }

	procedure errmsg( msg: ermsg; pos,lim: inbufptr );
	{ record error and position of error in line for later printing }
	var i: inbufptr;
	begin
	     listing := allowlist { force error line to be listed };
	     erset := erset + [msg];
	     errorcount := errorcount+1; { for posterity's sake }
	     for i := ermax+1 to pos-1 do erbuf[i] := ' ';
	     for i := pos to lim-1 do erbuf[i] := '=';
	     if lim > ermax+1 then ermax := lim - 1;
	end { error };

	procedure getline;
	{  read one line from the input file, initialize the
	    lexical analysis and listing control variables    }
	var i:inbufptr;
	    ch:char;

	    procedure makeend;
	    { put an end directive on the line as result of end file }
	    begin
		 line[1] := 'E';
		 line[2] := 'N';
		 line[3] := 'D';
		 i := 3;
	    end { makeend };

	    procedure getmac;
	    { get one line of text from the string pool copy of macro body }
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
		      end { while };
		      if ch <> pooldel then begin { isn't space in the line }
			   errmsg(notfit,0,0);
			   while strpool[gettext] <> pooldel
			     do gettext := gettext + 1;
			   gettext := gettext + 1;
		      end;
		      ch := strpool[gettext] { char after pooldel };
		      gettext := gettext + 1;
		      if ch in digits then begin { macro parameter }
			   parmnum := ord(ch)-ord('0');
			   if parmnum <= actcnt then begin { param exists }
				parm := actparm[parmnum];
				if parm > 0 then begin { param is nonblank }
				     ch := strpool[parm];
				     while (ch <> pooldel)
				       and (i < (linelen - 1)) do begin
					  i := i + 1;
					  line[i] := ch;
					  parm := parm + 1;
					  ch := strpool[parm];
				     end { loop copying text of parameter };
				     if ch <> pooldel then errmsg(notfit,0,0);
				end;
			   end;
			   ch := ' ' { force repeat loop to continue };
		      end;
		 until ch in [',',pooldel];
		 if ch = pooldel then makeend;
	    end { getmac };

	    procedure get(var f:text);
	    { read one line from appropriate input file }
	    begin
		 if eof(f) then begin
		      makeend;
		 end else begin
		      i := 0;
		      while ( not(eoln(f)) )and( i<(linelen-1) ) do begin
			   i := i+1;
			   read( f, ch );
			   if ch = pooldel then  ch := pdelrep;
			   line[i] := ch;
		      end;
		      if not(eoln(f)) then errmsg(notfit,0,0);
		      readln( f );
		 end;
	    end { get };

	begin { getline }
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
		  end { case };
		  { note that lines are only counted at the bottom level }
	     end;
	     length := i;
	     line[i+1] := ';' { this char must be initialized };
	     pos := 1;
	     lex.typ := eol;
	     lex.pos := 1;
	     lex.lim := 1;
	     next.typ := eol;
	     next.pos := 1;
	     next.lim := 1;
	     codelen := 0;
	end { getline };

	procedure settitle( var buf:linebuf;
			    var len:inbufptr;
			    pos,lim:inbufptr );
	{ fill the indicated title buffer with the indicated part
	   of the input line    				   }
	var i:inbufptr;
	begin
	     len := 0;
	     if lim-pos>ttlbuflen-3 then
		lim := pos+ttlbuflen-3;
	     for i:=1 to (ttlbuflen-(lim-pos+1)) div 2 do begin
		len := len+1;
		buf[len] := ' '
	     end;
	     for i := pos to lim do begin
		  len := len + 1;
		  buf[len] := line[i];
	     end;
	end { settitle };

	procedure newpage;
	{ force listing to the start of a new page }
	var ff:char;
	    i:inbufptr;
	begin
	     if lineonpg <> 1 then begin
		  ff := chr(12) { formfeed character };
		  writeln(o,ff);
		  { note that instead of using a formfeed, this routine
		     could be written to simply output blank lines and
		     count them with lineonpg until the count was high
		     enough to push the listing to a new page      }
		  lineonpg := 1;
		  pagenum := pagenum+1;

		  { write title to listing file }
		  write(o, 'SMAL32 Assembler, rev 12/88.       ' );
		  for i := 1 to titlelen do write(o, titlebuf[i] );
		  for i := titlelen to ttlbuflen do
		     write(o,' ');
		  writeln(o, timestr, '    Page ', pagenum:1 );
		  write(o, '                                    ' );
		  for i := 1 to sbttllen do write(o, sbttlbuf[i] );
		  for i := sbttllen to ttlbuflen do
		     write(o,' ');
		  writeln(o, datestr );
		  writeln(o);
	     end;
	end { newpage };

	procedure listline;
	{  list one line, including generated code.
	    if there are any errors, list the error messages  }
	var i:inbufptr;
	    msg:ermsg;
	    col,nextcol:integer { column on output listing };
	    codepos: integer; { more permanent buffer ptr }

	begin { listline }
	     lineonpg := lineonpg + 1;
	     if lineonpg >= linesper then
		  newpage;
	     col := 1;
	     codepos := 25; { in case we don't make any code.. }
	     if codelen > 0 then begin { list generated code }
		  if codeloc.base = abssym then write(o,' ')
					   else write(o,'+');
		  writehex( o, codeloc.offset,6 );
		  write(o,':');
		  col := 9;
		  i := 0;
		  while i < codelen do begin { list each code item }
		       i := i + 1;
		       with codebuf[i] do case form of
			    1: begin
				    nextcol := col+10;
				    if nextcol > listcol then begin
					 codepos := i;
					 i := codelen;
				    end else begin
					 if val.base<>abssym
					   then write(o,'+') else write(o,' ');
					 writehex(o,val.offset,8);
					 write(o,' ');
					 col := nextcol;
				    end;
			       end;
		       end { with  case };
		  end { while };
	     end { listing of generated code };
	     for col := col to listcol do write(o,' ');
	     write(o,lineno:6,' ');
	     { text starts in column listcol + 1 }
	     write(o,' ');
	     for i := 1 to length do write(o,line[i]);
	     { check for extended code listing }
	     
	     { list ALL generated code }
	     while codepos<=codelen do begin
		  with codebuf[codepos] do case form of
		       1: begin
			       nextcol := nextcol+10;
			       if nextcol > listcol then begin
				    writeln(o);
				    lineonpg := lineonpg + 1;
				    if lineonpg > linesper then newpage;
				    write(o,'        ');
				    nextcol := 9
			       end else begin
				    if val.base<>abssym
				      then write(o,'+') else write(o,' ');
				    writehex(o,val.offset,8);
				    write(o,' ');
				    codepos := codepos + 1;
			       end;
			  end;
		  end { with  case};
	     end { while };
	     { write out all accumulated error messages }
	     if erset <> [] then begin
		  for msg := minermsg to maxermsg do if msg in erset then begin
		       writeln(o);
		       lineonpg := lineonpg + 1;
		       if lineonpg > linesper then
			    newpage;
		       case msg of
			 baddig: write(o,'bad digit in number         ');
			 baddir: write(o,'invalid directive           ');
			 badrad: write(o,'bad radix                   ');
			 badrel: write(o,'misuse of relocation        ');
			 bounds: write(o,'value out of bounds         ');
			 comexp: write(o,'comma expected              ');
			 fwdref: write(o,'name used before definition ');
			 idexp:  write(o,'symbolic name expected      ');
			 maxuse: write(o,'too many use levels         ');
			 miseif: write(o,'missing endif               ');
			 misemc: write(o,'missing endmac              ');
			 misquo: write(o,'missing end quote           ');
			 muldef: write(o,'multiple label definition   ');
			 mulstt: write(o,'multiple start directives   ');
			 notfit: write(o,'text too long for line      ');
			 notlab: write(o,'not a label or directive    ');
			 notval: write(o,'bad value or expression     ');
			 parexp: write(o,'not a parenthesized list    ');
			 parovf: write(o,'too many macro parameters   ');
			 phase:  write(o,'label differed in pass 1    ');
			 quoexp: write(o,'quoted string expected      ');
			 unbal:  write(o,'unbalanced parentheses      ');
			 undef:  write(o,'undefined symbol            ');
			 unfunc: write(o,'invalid function            ');
			 unproc: write(o,'comment or eol expected     ');

		       end { case };

		       for col := 28 to listcol+7 do write(o,' ');
		       for i := 1 to ermax do write(o, erbuf[i] );
		       ermax := 0;
		  end { for };
	     end { if };
	     writeln(o);
	end { listline };

	procedure putobj( form: integer; offset: longint;
			  base: poolref );
	{  store value (offset,base) in current loc.
	    (base=abssym is used for absolute values; typically, relocatable
	     values will come from loc.base and loc.offset or expr.base and
	     expr.offset.)
	    use format form (1=word), save information for listing }
	begin
	     if allowlist then begin
		  { first assure that code gets loaded in right loc }
		  if (objloc.offset <> loc.offset) or (objloc.base <> loc.base)
		    then begin
		       objloc := loc;
		       write(obj,'.=');
		       genval(4,loc.offset,loc.base);
		  end;
		  { save appropriate listing data }
		  if codelen=0 then codeloc := loc;
		  if codelen < listcodes then begin
		       codelen := codelen + 1;
		       codebuf[codelen].val.offset := offset;
		       codebuf[codelen].val.base := base;
		       codebuf[codelen].form := form;
		  end;
		  { then generate correct object code }
		  case form of
		       1: begin
			       write(obj,'W');
			       genval(4,offset,base);
			       objloc.offset := add( objloc.offset, 1 );
			  end;
		  end;
	     end;
	     case form of
		  1: loc.offset := add( loc.offset, 1 );
	     end;
	end { putobj };


    { inside smal32.onepass, lexical analysis routines }

	procedure nextlex;
	{  save the next lexeme information in the current lexeme
	    variable, then read a new next one from the input line }
	var ch:char;
	    mark:char;

	    function number( radix: integer ): longint;
	    var acch,accl: longint   { accumulates the value };
		digit: integer       { the value of one digit };
	    begin
		 { assume initially that ch is a valid digit }
		 acch := 0;
		 accl := 0;
		 repeat
		      if ch in digits
			then digit := ord(ch) - ord('0')
			else if ch in upperc
			   then digit := ord(ch)-ord('A')+10
			   else digit := ord(ch)-ord('a')+10;

		      if digit >= radix then begin
			   ch := 'z';
			   acch := 65536;
		      end else begin
			   pos := pos + 1;
			   ch := line[pos];
			   accl := (accl * radix) + digit;
			   acch := (acch * radix) + (accl div 65536);
			   accl := accl mod 65536;
		      end;
		 until not(ch in (letters+digits)) or (acch >= 65536);
		 if ch in letters then begin
		      while ch in (letters+digits) do begin
			   pos := pos + 1;
			   ch := line[pos];
		      end;
		      errmsg(baddig,next.pos,pos);
		      number := 0;
		 end else if acch >= 65536 then begin
		      while ch in (letters+digits) do begin
			   pos := pos + 1;
			   ch := line[pos];
		      end;
		      errmsg(bounds,next.pos,pos);
		      number := 0;
		 end else if acch >= 32768 then begin
		      number := (-maxposint-1) +
				(65536 * (acch - 32768)) + accl;
		 end else begin
		      number := (65536 * acch) + accl;
		 end;
	    end { number };

	begin { nextlex }
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
		       '(': next.typ := bpar;
		       ')': next.typ := epar;
		  end { case };
		  pos := pos+1;
	     end else if ch in digits then begin
		  next.typ := num;
		  next.val := number(10);
		  if ch = '#' then begin
		       if (next.val > 36) or (next.val < 2) then begin
			    next.val := 36;
			    errmsg(badrad,next.pos,pos);
		       end;
		       pos := pos + 1;
		       ch := line[pos];
		       if ch in (letters+digits)
			 then next.val := number(next.val)
			 else errmsg(baddig,next.pos,pos);
		  end;
	     end else if ch in letters then begin
		  next.typ := id;
		  repeat
		       pos := pos+1;
		       ch := line[pos];
		  until not(ch in (digits + letters));
	     end else if ch = '#' then begin
		  pos := pos + 1;
		  ch := line[pos];
		  if ch in hexdigits then begin
		       next.typ := num;
		       next.val := number(16);
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
		       errmsg(misquo,next.pos,next.pos+1);
		  end;
	     end else begin { invalid lexeme }
		  repeat
		       pos := pos+1;
		       ch := line[pos];
		  until ch in valid;
		  next.typ := junk;
	     end;
	     next.lim := pos;
	end { nextlex };

	procedure startup;
	{ setup for processing one line of input }
	begin
	     getline { read input line };
	     nextlex { read first lexeme };
	     nextlex { read second lexeme (allow lookahead) };
	     { start parsing by looking for valid start of line }
	     while not(lex.typ in [id,eol,dot]) do begin
		  errmsg(notlab,lex.pos,lex.lim);
		  nextlex;
	     end;
	end { startup };

    { inside smal32.onepass, string pool and symbol table management }

	procedure putch( ch:char );
	{ put one char into permanent end of stringpool }
	begin
	     if poolsp > poolpos then begin { there is room in pool }
		  poolpos := poolpos + 1;
		  strpool[poolpos] := ch;
	     end else begin { there isn't room }
		  poolfull := true;
	     end;
	end { putch };

	function putpool( pos,lim:inbufptr ): poolref;
	{ put the string between pos and lim-1 on the current line into
	   the string pool, returning it's index in the pool.  the string
	   delimiter is appended to the string in the pool.  it is assumed
	   that the string will fit (the caller must guarantee this)    }
	var i:inbufptr;
	begin
	     poolpos := poolpos + 1;
	     putpool := poolpos;
	     for i := pos to lim-1 do begin
		  strpool[poolpos] := line[i];
		  poolpos := poolpos + 1;
	     end;
	     strpool[poolpos] := pooldel;
	end { putpool };

	function poolfit(pos,lim: inbufptr): boolean;
	{ check to see if text between pos and lim will fit in stringpool }
	begin
	     poolfit := ( (poolsp - poolpos) > (lim - pos) );
	end { poolfit };

	function poolcmp( poolpos:poolref; pos,lim:inbufptr ):boolean;
	{ compare the string starting at poolpos in the stringpool with
	   that between pos and lim on the current line, return true if
	   they are the same; this relies on the fact that the string
	   delimiter in the stringpool will never occur in the line   }
	begin
	     while strpool[poolpos] = line[pos] do begin
		  poolpos := poolpos + 1;
		  pos := pos + 1;
	     end;
	     poolcmp := (strpool[poolpos] = pooldel) and (pos = lim);
	end { poolcmp };

	function hash( pos,lim: inbufptr; modulus: integer): integer;
	{ compute hash of lexeme between pos and lim,
	   return a value between 1 and modulus (inclusive)
	   this hash function must match that in "opinit"  }
	var acc: integer;
	    p: inbufptr;
	begin
	     acc := 1;
	     for p := pos to lim-1
	       do acc := (((acc*5) + ord(line[p])) mod modulus) + 1;
	     hash := acc;
	end { hash };

	function lookup( pos,lim: inbufptr ): symptr;
	{ find the symbol between pos and lim on the current line in
	   the symbol table, return the index into the table where it
	   was found or inserted; if it could not be inserted, return
	   zero 						     }
	var s,olds: symptr;
	begin
	     s := hash(pos,lim,symsize);
	     olds := s;
	     lookup := 0 { default return value };
	     repeat
		  with symtab[s] do begin
		       if id<>0 then begin
			    if poolcmp(id,pos,lim) then begin
				 lookup := s;
				 s := olds  { terminate loop };
			    end else begin
				 if s < symsize
				   then s := s + 1
				   else s := 1;
				 if s = olds then symfull := true;
			    end;
		       end else begin { found unused table entry }
			    if poolfit(pos,lim) then begin
				 { put the symbol in the pool and table }
				 id := putpool(pos,lim);
				 lookup := s;
			    end else begin { no room in pool for sym }
				 poolfull := true;
			    end;
			    s := olds { terminate loop };
		       end { if };
		  end { with };
	     until s = olds;
	end { lookup };

	function oplookup( pos,lim: inbufptr ): opptr;
	{ find the symbol between pos and lim on the current line in
	   the opcode table, return the index into the table where it
	   was found or should be put; return 0 if it isn't found and
	   the table is full    				     }
	var s,olds:opptr;

	begin
	     s := hash(pos,lim,opcodes);
	     olds := s;
	     oplookup := 0 { default return value };
	     repeat
		  with optab[s] do begin
		       if id<>0 then begin { have nonblank entry }
			    if poolcmp(id,pos,lim) then begin { found it }
				 oplookup := s;
				 s := olds { terminate loop };
			    end else begin
				 if s < opcodes
				   then s := s + 1
				   else s := 1;
			    end;
		       end else begin { found vacancy }
			    oplookup := s;
			    s := olds { terminate loop };
		       end;
		  end { with };
	     until s = olds;
	end { oplookup };


    { inside smal32.onepass, utility parsing procedures }

	procedure getcomma;
	{ skip the comma, complain if there isn't one }
	begin
	     if lex.typ = comma
	       then nextlex
	       else errmsg(comexp,lex.pos,lex.lim);
	end { getcomma };

	procedure skipbal;
	{ skip to maching end paren when given begin paren }
	var nest:integer;
	    par:lexeme;
	begin
	     { assert lex.typ = bpar }
	     nest := 1;
	     par := lex;
	     repeat
		  nextlex;
		  if lex.typ = bpar
		    then nest := nest + 1
		    else if lex.typ = epar
			   then nest := nest - 1;
	     until (nest < 1) or (lex.typ = eol);
	     if lex.typ = eol then errmsg(unbal,par.pos,par.lim);
	end { skipbal };



    { inside smal32.onepass, procedures to parse expressions }

	procedure expression;
	{ parse expressions of the form
		<expression> ::= <term> ! <expression> <binop> <term>
	   return the value of the expression in expr }
	var acc: value  	  { the accumulator };
	    accdef: boolean       { is the accumulator defined };
	    accundef: boolean     { does acc. have fwd ref(s)? };
	    op: lexeme  	  { what operator was found };
	    expos: inbufptr       { position of start of expression };

	    procedure term;
	    { parse terms of an expression of the form
		    <term> ::= [ <unary> ] <value>
	       return the value of the term in expr }
	    var op:lexeme { unary operator };

		procedure value;
		{ parse values of an expression of the form
			<value> ::= <ident> ! <num> ! . ! ( <expression> )
				  ! <string> ! <identifier> ( <argument> )
		   return the value of the value in expr }
		var symbol: symptr;
		    op: lexeme;
		    par: lexeme;
		    i: integer;
		    funcdfop, funcfwop, functyop, funcleop: boolean;
		   {  above are flags for function recognition  }
		begin { proc. -value- }
		     exprpos := lex.pos;
		     exprlim := lex.lim;
		     exprundef := false;
		     if lex.typ = num then begin  { got a number }
			  expr.offset := lex.val;
			  expr.base := abssym;
			  exprdef := true;
			  nextlex { read over number };
		     end else if (lex.typ = quote) then begin { got string }
			  expr.base := 0;
			  exprdef := true;
			  i := lex.lim - lex.pos;
			  if i>6 then errmsg(bounds,lex.pos,lex.lim);
			  expr.offset := 0;
			  if i>2 then
			      for i:=1 to lex.lim-lex.pos-2 do
				 expr.offset := 256*expr.offset +
						ascii[line[lex.pos+i]];
			  nextlex;
		     end else if (lex.typ = id) then begin
			  funcdfop := false;
			  funcfwop := false;
			  functyop := false;
			  funcleop := false;
			  if next.typ=bpar then with lex do
			     if poolcmp(funcdf,pos,lim) then
				funcdfop := true
			     else if poolcmp(funcfw,pos,lim) then
				funcfwop := true
			     else if poolcmp(functy,pos,lim) then
				functyop := true
			     else if poolcmp(funcle,pos,lim) then
				funcleop := true;
			    {  else, assume regular identifier,
				and ignore trailing bpar	 }

			  if funcdfop or funcfwop or
			     functyop or funcleop then begin
			    {  do a named (unary) function  }
			     op := lex;
			     nextlex { skip operator name };
			     par := lex;
			     nextlex { skip opening paren };
			     expr.base := abssym;
			     expr.offset := 1 { default to ambiguous };
			     exprdef := true  { default to defined };
			     if funcdfop then begin
				  if lex.typ = id then begin
				       symbol := lookup(lex.pos,lex.lim);
				  end else begin
				       symbol := 0;
				       errmsg(idexp,lex.pos,lex.lim);
				  end;
				  nextlex { skip operand };
				  if symbol <> 0 then expr.offset
				    := -ord(setyet in symtab[symbol].use);
			     end else if funcfwop then begin
				  if lex.typ = id then begin
				       symbol := lookup(lex.pos,lex.lim);
				  end else begin
				       symbol := 0;
				       errmsg(idexp,lex.pos,lex.lim);
				  end;
				  nextlex { skip operand };
				  if symbol <> 0 then expr.offset
				    := -ord(   (usedyet in symtab[symbol].use)
					 and not(setyet in symtab[symbol].use));
			     end else if functyop then begin
				  expression;
				  expr.offset := expr.base;
				  expr.base := abssym;
			     end else if funcleop then begin
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
			     end;
			     if lex.typ = epar then begin
				  exprpos := op.pos;
				  exprlim := lex.lim;
				  nextlex { skip end paren };
			     end else begin
				  errmsg(unbal,par.pos,par.lim);
			     end;
			  end else begin
			    {  ah, just an ordinary identifier..  }
			     symbol := lookup(lex.pos,lex.lim);
			     if symbol > 0 then with symtab[symbol] do begin
				  use := use + [usedyet];
				  if (def in use) or (lab in use) then begin
				       expr := val;
				       exprdef := true;
				       exprundef := not (setyet in use);
				  end else begin
				       errmsg(undef,lex.pos,lex.lim);
				       expr.offset := 0;
				       expr.base := abssym;
				       exprdef := false;
				  end;
			     end else begin
				  expr.offset := 0 { no err on full table };
				  expr.base := abssym;
				  exprdef := true { pretend it's defined };
			     end { if };
			     nextlex { read over identifier };
			  end
		     end else if lex.typ = dot then begin
			  expr := loc;
			  exprdef := true;
			  nextlex { read over dot };
		     end else if lex.typ = bpar then begin
			  par := lex;
			  nextlex;
			  expression;
			  if lex.typ = epar then begin
			       exprpos := par.pos;
			       exprlim := lex.lim;
			       nextlex;
			  end else begin
			       errmsg(unbal,par.pos,par.lim);
			  end;
		     end else begin   { got something else }
			  errmsg(notval,lex.pos,lex.lim);
			  expr.offset := 0;
			  expr.base := abssym;
			  exprdef := false;
			  if not(lex.typ in [epar,eol,comma])
			    then nextlex { read over whatever it is };
		     end;
		     exprundef := (not exprdef) or exprundef;
		end { value };

	    begin { term }
		 if lex.typ in [plus,minus,notsym] then begin { unary }
		      op := lex;
		      nextlex { read over unary operator };
		      value { get value to be modified };
		      exprpos := op.pos;
		      case op.typ of
		       plus:  ;
		       minus: if expr.base = abssym
				then expr.offset := neg(expr.offset)
				else errmsg(badrel,op.pos,op.lim);
		       notsym:if expr.base = abssym
				then expr.offset := inot(expr.offset)
				else errmsg(badrel,op.pos,op.lim);
		      end { case };
		 end else begin { no unary operator }
		      value;
		 end;
	    end { term };

	begin { expression };
	     term { get leading term };
	     acc := expr;
	     accdef := exprdef;
	     accundef := exprundef;
	     expos := exprpos { save pos for error handlers };
	     while (lex.typ in [plus,minus,gt,lt,eq,andsym,orsym]) do begin
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
				    errmsg(badrel,op.pos,op.lim);
				    acc.base := abssym;
			       end;
			  end { plus };
		   minus: begin
			       acc.offset := sub(acc.offset,expr.offset);
			       if acc.base = expr.base then begin
				    acc.base := abssym
			       end else if expr.base <> abssym then begin
				    errmsg(badrel,op.pos,op.lim);
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
			       errmsg(badrel,op.pos,op.lim);
			       acc.base := abssym;
			       acc.offset := 1 { neither true nor false };
			  end { gt,lt,eq };
	    andsym,orsym: if (acc.base=abssym)and(expr.base=abssym) then begin
			       case op.typ of
			      andsym: acc.offset:=iand(acc.offset,expr.offset);
			       orsym: acc.offset:=ior(acc.offset,expr.offset);
			       end { case };
			  end else begin
			       errmsg(badrel,op.pos,op.lim);
			  end { andsym,orsym };
	       bpar,epar: if (acc.base=abssym)and(expr.base=abssym) then begin
			       if expr.offset > 32 then expr.offset := 32;
			       while expr.offset > 0 do begin
				     with acc do case op.typ of
				   bpar: offset := add( offset, offset );
				   epar: offset := rightshift( offset );
				     end;
				     expr.offset := expr.offset - 1;
			       end;
			  end else begin
			       errmsg(badrel,op.pos,op.lim);
			  end { shift operators }
		  end { case };
	     end { while loop processing terms };
	     expr := acc;
	     exprdef := accdef;
	     exprundef := exprundef or accundef or (not exprdef);
	     exprpos := expos;
	end { expression };

	procedure expresbal;
	{ evaluate expressions, assuring balanced parens }
	begin
	     expression;
	     while lex.typ = epar do begin
		  errmsg(unbal,lex.pos,lex.lim);
		  nextlex;
	     end;
	end { expresbal };

	function predicate: boolean;
	{ evaluate predicates for if and elseif directives }
	begin
	     expresbal { evaluate expression };
	     predicate := false { default };
	     if expr.base = abssym then begin
		  if expr.offset = -1
		    then predicate := true;
	     end else begin
		  errmsg(badrel,exprpos,exprlim);
	     end;
	end { predicate };


    { inside smal32.onepass, processing of key syntactic elements }

	procedure labeldef;
	{ parse label definition; define label and handle multiples }
	var symbol: symptr;
	begin
	     { assume that (lex.typ = id) and (next.typ = colon) }
	     symbol := lookup( lex.pos, lex.lim );
	     if symbol > 0 then begin { the symbol is in the table }
		  with symtab[symbol] do begin
		       if (setyet in use) then begin
			    errmsg(muldef,lex.pos,lex.lim);
		       end else if (lab in use) then begin
			    if (val.offset<>loc.offset)or(val.base<>loc.base)
			      then errmsg(phase,lex.pos,lex.lim);
		       end else begin
			    val := loc;
		       end;
		       use := use + [lab,setyet];
		  end;
	     end;
	     nextlex { read over id };
	     nextlex { read over colon };
	end { labeldef };

	procedure definition;
	{ parse and process definition of form <id> = <expression> }
	var symbol: symptr;
	begin
	     symbol := lookup( lex.pos, lex.lim );
	     if lab in symtab[symbol].use then errmsg(muldef,lex.pos,lex.lim);
	     nextlex { read over id };
	     nextlex { read over eq };
	     expresbal;
	     if symbol > 0 then with symtab[symbol] do begin
		  use := use + [setyet];
		  if exprdef then begin
		       use := use + [def];
		       val := expr;
		  end;
	     end;
	end { definition };

	procedure origin;
	{ parse and process definitions of the form . = <expression> }
	begin
	     nextlex { skip dot };
	     nextlex { skip eq };
	     expresbal;
	     loc := expr;
	end { origin };

	procedure opcode;

	 {  parse opcode field, including detection of data width
	   specifying suffices.  Resultant info is returned via globals
	   optype, opval, opsubt, opsufi, opsufi2, opsuff and opsufcc. }

	var   i: opptr;

	begin { opcode }
	    oppos := lex.pos;
	    oplim := lex.lim;
	    optype := operr;

	    i := oplookup(oppos,oplim);
	    if i<>0 then begin
	       if optab[i].id<>0 then  with optab[i] do begin
		  optype := typ;
		  opval := val;
		  opsubt := subtyp;
	       end;
	    end;

	    nextlex;
	end { opcode };


	procedure getop;
	{ skip and ignore labels on a line, return the opcode globally 
	   suppress any error messages encountered in parsing the line }
	begin
	     startup;
	     while (lex.typ = id) and (next.typ = colon) do begin
		  nextlex { skip id };
		  nextlex { skip colon };
	     end;
	     if lex.typ = id then begin
		  if next.typ = eq
		    then optype := operr
		    else opcode;
	     end else optype := operr;
	     erset := [];
	end { getop };


    { inside smal32.onepass, processing of external symbol linkages }

	procedure internl;
	{ parse and process internal symbol definitions }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then with symtab[symbol] do begin
		       use := use + [intdef];
		       if (use * [def,lab]) = []
			 then errmsg(undef,lex.pos,lex.lim);
		  end { if with };
	     end else begin
		  errmsg(idexp,lex.pos,lex.lim);
	     end;
	     nextlex { read over internal symbol name };
	end { internl };

	procedure makeext(symbol:symptr);
	{ make or verify that the current symbol is external }
			   { used only from externl and comdef }
	begin
	     with symtab[symbol] do begin
		  if (setyet in use) then begin
		       errmsg(muldef,lex.pos,lex.lim);
		  end else if (usedyet in use) then begin
		       errmsg(fwdref,lex.pos,lex.lim);
		  end else if (lab in use) then begin
		       if (val.base <> id) or (val.offset <> 0)
			 then errmsg(muldef,lex.pos,lex.lim);
		  end else begin { symbol previously unused }
		       val.base := id;
		       val.offset := 0;
		  end;
		  use := use + [lab,setyet];
	     end { with };
	end { makeext };

	procedure externl;
	{ parse and process external symbol declarations }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then makeext(symbol);
	     end else begin
		  errmsg(idexp,lex.pos,lex.lim);
	     end;
	     nextlex { read over external symbol name };
	end { externl };

	procedure comdef;
	{ parse and process common declarations }
	var symbol:symptr;
	begin
	     if lex.typ = id then begin
		  symbol := lookup(lex.pos,lex.lim);
		  if symbol > 0 then with symtab[symbol] do begin
		       makeext(symbol);
		       nextlex { read over common name };
		       getcomma;
		       expresbal { get common size or maximum location };
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
			    errmsg(badrel,exprpos,exprlim);
		       end;
		  end else begin { symbol table full }
		       nextlex { skip over name };
		       getcomma;
		       expresbal { skip over size };
		  end;
	     end else begin { common name missing }
		  errmsg(idexp,lex.pos,lex.lim);
	     end;
	end { comdef };


    { inside smal32.onepass, processing of text insertions }

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
		       {1: reset(inp1,infile[1]); -- this will never happen }
			2: reset(inp2,infile[2]);
			3: reset(inp3,infile[3])
		       end;
		  end else begin
		       errmsg(maxuse,lex.pos,lex.lim);
		  end;
	     end else begin
		  errmsg(quoexp,lex.pos,lex.lim);
	     end;
	     nextlex { read over file name };
	end { insert };

	procedure macdef;
	{ process macro definitions of the form:
	       macro <name> [ <param> [ , <param> ]* ] <body>          }
	var m:opptr;
	    parmtab: array [1..parmlim] of poolref;
	    parms: 0..parmlim;
	    oldsp: poolref;

	    procedure getpar;
	    { parse one formal parameter of form:
		  <param> := <id>  !  ( <id> )  !  = <id>
	       corresponding to by name, by list of names, and by value }
	    var parm: lexeme { the parameter identifier };
		par: lexeme  { the position of the begin paren };
		typ: char    { the type of the formal parameter };
	    begin { getpar };
		 if parms < parmlim then begin
		      if lex.typ = id then begin { name parameter }
			   parm := lex;
			   typ := 'a';
		      end else if lex.typ = eq then begin { value param }
			   nextlex;
			   if lex.typ = id then begin
				parm := lex;
				typ := '=';
			   end else begin
				parm.typ := eol;
				errmsg(idexp,lex.pos,lex.lim);
			   end;
		      end else if lex.typ = bpar then begin { value parm }
			   par := lex { hold onto position for errors };
			   nextlex { skip over paren };
			   if lex.typ = id then begin
				parm := lex;
				typ := '(';
				nextlex { skip over identifier };
				if lex.typ <> epar
				  then errmsg(unbal,par.pos,par.lim);
			   end else begin
				parm.typ := eol;
				errmsg(idexp,lex.pos,lex.lim);
			   end;
		      end else begin { bad parameter }
			   parm.typ := eol;
			   errmsg(idexp,lex.pos,lex.lim);
		      end;
		      if parm.typ = id then begin { have a good param }
			   parms := parms + 1;
			   if firstpass then begin
				parmtab[parms] := pushtext(parm.pos,parm.lim);
				putch(typ);
			   end;
		      end;
		 end else begin { too many parameters }
		      errmsg(parovf,lex.pos,lex.lim);
		 end { processing one parameter };
		 nextlex { read over parameter };
	    end { getpar };

	    procedure getbody;
	    { parse macro body of form: <body> ::= <linesequence> endmac }
	    type parm=0..parmlim;
	    var nest:integer  { counter to find right endmac when nested };
		pos,lim:inbufptr  { progress pointers for parameter scan };
		parmnum:parm  { identity of current parameter };

		function lookup(pos,lim:inbufptr):parm;
		{ lookup candidate formal parameter name }
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
		end { lookup };

	    begin { getbody }
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
		      if (nest > 0) and firstpass then begin { save text }
			   pos := 1;
			   while pos <= length do begin
				while not(line[pos] in letters)
				  and (pos <= length) do begin
				     if line[pos] = '''' then begin
					  pos := pos + 1;
					  { assert line[length+1] = ';' }
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
				     while line[lim] in letters + digits
				       do lim := lim + 1;
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
			   end { while };
			   putch(pooldel);
			   putch(',');
		      end { one line of text was stored };
		 until nest < 1;
		 poolsp := oldsp { pop formal parameter table from stack };
		 if optype = opend then begin { found end of file, not endm }
		      errmsg(misemc,0,0);
		      popget;
		 end;
		 if firstpass then begin
		      putch(pooldel);
		      putch(pooldel) { two pooldel's in a row end a macro };
		 end;
	    end { getbody };

	begin { macdef }
	     parms := 0;
	     oldsp := poolsp { mark stack top, allowing temporary use };
	     if lex.typ = id then begin { have macro name }
		  m := oplookup(lex.pos,lex.lim);
		  if m <= 0 then begin { no room in table }
		       opfull := true;
		  end else if firstpass then begin { define macro name }
		       if (optab[m].id=0) then begin { first definition }
			    if poolfit(lex.pos,lex.lim) then begin
				 optab[m].id := putpool(lex.pos,lex.lim);
				 optab[m].typ := opmcall;
				 optab[m].val := poolpos + 1;
			    end;
		       end else begin { redefinition }
			    optab[m].typ := opmcall;
			    optab[m].val := poolpos + 1;
		       end;
		  end;
		  nextlex { skip over macro name };
		  if lex.typ <> eol then begin
		       getpar;
		       while lex.typ <> eol do begin
			    getcomma;
			    getpar;
		       end;
		  end;
		  if firstpass then putch(pooldel) { mark end of parmtypes };
	     end else begin { missing macro name }
		  errmsg(idexp,lex.pos,lex.lim);
		  nextlex { skip over junk };
	     end { processing macro header };
	     if (lex.typ <> eol) and (erset = [])
	       then errmsg(unproc,lex.pos,lex.lim);
	     getbody;
	end { macdef };

	procedure maccall( poolpos: poolref );
	{ call macro who's text is stored at poolpos in string pool;
	   form of call is:
	   <name> [ <param> [ , <param> ]* ]    		  }

	    procedure getpar;
	    { parse a parameter of the form:
	       <param> ::= [ <lexeme> ]*
			!  <expression>
			!  ( [ <lexeme> ]* ) [ : <expr> [ : <expr> ] ]  }
	    var typ:char { indicates expected parameter type };
		pos,lim:inbufptr { location of parameter };
		par:lexeme { position info for begin paren };
	    begin
		 typ := strpool[poolpos];
		 poolpos := poolpos + 1;
		 actcnt := actcnt + 1;
		 if lex.typ in [comma,eol] then begin { parameter missing }
		      actparm[actcnt] := 0;
		 end else if typ = 'a' then begin
		      pos := lex.pos;
		      lim := lex.lim;
		      while not(lex.typ in [eol,comma]) do begin
			   if lex.typ = bpar
			     then skipbal
			     else if lex.typ = epar
				    then errmsg(unbal,lex.pos,lex.lim);
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
			   nextlex { skip paren at list head };
			   pos := lex.pos;
			   lim := pos { default for empty string };
			   while not(lex.typ in [eol,epar]) do begin
				if lex.typ = bpar then skipbal;
				lim := lex.lim;
				nextlex;
			   end;
			   if lex.typ = eol
			     then errmsg(unbal,par.pos,par.lim)
			     else nextlex;
			   if lex.typ = colon then begin { substring }
				nextlex;
				if lex.typ <> colon then begin
				     expresbal { get start };
				     if expr.base <> abssym
				       then errmsg(badrel,exprpos,exprlim);
				     if expr.offset > 1 then begin
					  if expr.offset > (lim - pos)
					    then pos := lim
					    else pos := pos + expr.offset - 1;
				     end;
				end;
				if lex.typ = colon then begin
				     nextlex;
				     expresbal { get length };
				     if expr.base <> abssym
				       then errmsg(badrel,exprpos,exprlim);
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
			   errmsg(parexp,lex.pos,lex.lim);
			   nextlex;
		      end;
		 end;
	    end { getpar };

	begin { maccall }
	     pushget { save previous macro expansion status block };
	     actcnt := 0;
	     while (strpool[poolpos] <> pooldel) and (lex.typ <> eol) do begin
		  getpar;
		  if lex.typ <> eol then getcomma;
	     end;
	     if lex.typ <> eol then errmsg(parovf,lex.pos,lex.lim);
	     while strpool[poolpos] <> pooldel do poolpos := poolpos + 1;
	     gettext := poolpos + 1 { set it to read macro text from pool };
	   { ***** the following caused label "phase error" probs. }
	   {if (erset <> []) or poolfull then popget}{ stop bad calls }
	end { maccall };


    { inside smal32.onepass, processing of conditional directives }

	procedure findend;
	{ skip over lines until a line with endif or end opcode found }
	var nest:integer;
	begin
	     nest := 0;
	     repeat { read and check following lines }
		  if listing then listline { first list previous line };
		  getop;
		  if optype = opif 
		    then nest := nest + 1
		    else if optype = opendif
			   then nest := nest - 1;
	     until (optype = opend) or (nest < 0);
	     if optype = opend then begin
		  errmsg(miseif,0,0);
		  popget;
	     end;
	end { findend };

	procedure findelse;
	{ skip lines until one with an else, elseif <true>, or end found }
	begin
	     repeat { read over then parts (allowing multiple elseif's) }
		  if (lex.typ <> eol) and (erset = [])
		    then errmsg(unproc,lex.pos,lex.lim);
		  repeat
		       if listing then listline { list line to be skipped };
		       getop;
		       while (optype = opif) do begin;
			    findend;
			    if listing then listline { list end };
			    if optype=opend
			      then optype := opendif { don't complain twice }
			      else getop;
		       end;
		  until optype in [opend,opendif,opelse,opelseif];
		  if (optype = opelseif) then begin
		       if predicate then optype := opelse;
		  end;
	     until optype in [opend,opendif,opelse];
	     if optype = opend then begin
		  errmsg(miseif,0,0);
		  popget;
	     end;
	end { findelse };


{ inside smal32.onepass }

    begin { onepass }
	 upperc := ['A'..'Z'];
	 letters := ['a'..'z'] + upperc;
	 digits := ['0'..'9'];  { these four ought to be constants }
	 hexdigits := ['a'..'f','A'..'F'] + digits;
	 lexpunc := [ ':', '.', ',', '=', '>', '<', '+', '-', '\',
		      '@', '&', '!', '(', ')', '[', ']' ];
	 quotemarks := ['''','"'];
	 valid := letters + quotemarks + digits + lexpunc + [' ',';','#'];

	 poolsp := poolsize;
	 gettext := 0;
	 getlevel := 0;
	 oldsp := 0;
	 actcnt := 0;
	 pushget { put a dummy level on the stack to allow clean end };
	 getlevel := 1 { setup for reading at normal source level };
	 listlevel := 1 { setup so it will list only main level source };
	 lineonpg := linesper; { force leading page-eject.. }
	 lineno := 0;
	 errorcount := 0;
	 loc.offset := 0;
	 loc.base := relsym;
	 maxrel := 0;
	 objloc := loc;
	 seenstart := false;
	 clearuse { setup symbol table for pass };

	 while getlevel >= 1 do begin
	      listing := (listlevel > 0) and (allowlist);
	      startup { setup for processing a line };

	      while (lex.typ = id) and (next.typ = colon) do labeldef;

	      { now know that if lex.typ = id, then next.typ <> colon }
	      if lex.typ = id then begin
		   if next.typ = eq then begin { process definitions }
			definition;
		   end else begin
			opcode;
			case optype of { find out what class of opcode }
			operr: errmsg(baddir,oppos,oplim);
			  opd: begin { 32 bit double-word }
				    expresbal;
				    putobj(1,expr.offset,expr.base);
				    while lex.typ = comma do begin
					 nextlex;
					 expresbal;
					 putobj(1,expr.offset,expr.base);
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
		       opendm: errmsg(baddir,oppos,oplim);
			opuse: insert  { insert text from alt file };
		       oplist: begin { control listing }
				    expresbal;
				    if expr.base <> abssym then begin
					 errmsg(badrel,exprpos,exprlim);
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
				    end;
				    lex.typ := eol;
			       end;
		      opeject: if listing then lineonpg := linesper - 1;
		      opstart: if not seenstart then begin { set start addr }
				    seenstart := true;
				    expresbal;
				    startloc := expr;
			       end else begin { multiple start addr's }
				    errmsg( mulstt, oppos, oplim );
			       end;
			opend: popget;
		      opmcall: maccall(opval) { call the indicated macro };
			end { case optype for opcode classes };
		   end { if };
	      end else if (lex.typ = dot) and (next.typ = eq) then begin
		   origin;
	      end else if lex.typ <> eol then begin
		   errmsg(baddir,lex.pos,lex.lim);
		   nextlex { skip over junk to avoid complaining twice };
	      end;
	      if (lex.typ <> eol) and (erset = [])
		then errmsg(unproc,lex.pos,lex.lim);
	      if listing then listline;
	      if loc.base = relsym
		then if ugt( loc.offset, maxrel )
		       then maxrel := loc.offset;
	 end { while };
	 if allowlist then begin
	     { make sure object code ends at maxrel }
	      if (loc.base <> relsym) or (loc.offset <> maxrel) then begin
		   write(obj,'.=');
		   genval(4,maxrel,relsym);
	      end;
	      { put starting address out }
	      if seenstart then begin
		   write(obj,'S');
		   genval(4,startloc.offset,startloc.base);
	      end;
	     { note error count in listing }
	      if errorcount=0 then
		  writeln(o, '                    no errors')
	      else if errorcount=1 then
		  writeln(o, '     1 error in this assembly')
	      else
		  writeln(o, '     ', errorcount:1,
			  ' errors in this assembly');
	 end;
    end { onepass };


{ inside smal32, procedures to do file setup and takedown }

    procedure getfiles;
    {  read file name from terminal, store it in global "infile"
	suffix it with ".l" and ".o" and store it in "outfile" and "objfile" }
    var i: 1..33;
	j: 0..33;
	ch: char;
    begin
	 writeln;
	 write('  input file name: ');
	 i := 1;
	 j := 0;
	 while not(eoln(input)) and (i<=30) do begin
	      read(ch);
	      infile[1][i] := ch;
	      titlebuf[i] := ch;
	      if ch = '.' then j := i;
	      i := i+1;
	 end;
	 readln;
	 titlelen := i-1;
	 sbttllen := 0;
	 if j = 0 then j := i;
	 for i := i to 32 do infile[1][i]:= ' ';
	 outfile := infile[1];
	 outfile[j] := '.';
	 outfile[j+1] := 'l';
	 for i := j+2 to 32 do outfile[i]:= ' ';
	 objfile := outfile;
	 objfile[j+1] := 'o';
    end { getfiles };


{ inside smal32 }

begin { smal32 }
    { test implementation characteristics }
     if maxint < maxposint then
	writeln('*** integers too smal32l ***');
     if ((-maxposbit)*2)+1 <> -maxposint then
	writeln('*** minus numbers too smal32l ***');
    { assume that overflow will be detected }

     initascii;
     getfiles;
     reset(inp1,infile[1]);
     rewrite(o,outfile);
     rewrite(obj,objfile);
     clearsym;
     opinit;
     lineonpg := 1;
     onepass( { firstpass } true, { allowlist } false );
     reset(inp1,infile[1]);
     writeln(obj,'R=.');
     onepass( { firstpass } false, { allowlist } true );
     objsufx;
     writeln;
     if errorcount=0 then
	 writeln('   no errors')
     else if errorcount=1 then
	 writeln('   1 error')
     else
	 writeln('   ', errorcount:1, ' errors');
     if symfull then writeln('** symbol table overflowed **');
     if poolfull then writeln('** string pool overflowed **');
     if opfull then writeln('** macro name table full **');
end { smal32 }.
