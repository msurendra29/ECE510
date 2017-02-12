// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Instructor :  Tareque Ahmad
//   Project Team: Surendra Maddula, Bharath Reddy Godi.
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     ifd_checker.sv
//   Description:  Checker for the IFD Unit
//   Created by:   Surendra Maddula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================
import pdp8_pkg::*; // Importing contents from package pdp8_pkg

`include "pdp8_pkg.sv"

module ifd_checker
  (
   // Global inputs
   input clk,
   input reset_n,

   // From Execution unit to IFD
   input stall,
   input [`ADDR_WIDTH-1:0] PC_value,

   // To memory unit from IFD
   input                    ifu_rd_req,
   input  [`ADDR_WIDTH-1:0] ifu_rd_addr,

   // From memory unit to IFD
   input [`DATA_WIDTH-1:0] ifu_rd_data,

   // To Execution unit (decode struct) from IFD
   input [`ADDR_WIDTH-1:0] base_addr,
   input pdp_mem_opcode_s pdp_mem_opcode,
   input pdp_op7_opcode_s pdp_op7_opcode
   );
reg unsupported;
reg                   new_mem_opcode; // Signal to detect a new memory instruction
reg                   new_op7_opcode; // Signal to detect a new op7 instruction
reg                   new_opcode1; 
reg flag, flag_f1;

reg first_instruction,last_instruction;
reg [4:0]opcode_count;

time current_time;
parameter BASE_ADDRESS = 12'o200,
SET = 1'b1,
CLEAR = 1'b0,
CLEAR_DATA = 12'd0;


pdp_mem_opcode_s A, int_op_mem, temp_pdp_mem_opcode;
pdp_op7_opcode_s B, int_op7,temp_pdp_op7_opcode;




//After reset_n is asserted low to high base_address should be set to a start address(octal 200)

`ifndef DISABLE_RULE1

property R1;

	@(posedge clk) $rose(reset_n)|-> (base_addr == BASE_ADDRESS);

endproperty

assert property(R1)
		//$display("Rule 1 passed");
		else $error("Rule 1 Failed");


C1: cover property(R1);

`endif





//After reset_n is asserted low to high ifu_rd_req, ifu_rd_addr,pdp_mem_opcode and pdp_op7_opcode should be as below.
`ifndef DISABLE_RULE2

property R2;
	@(posedge clk) $rose(reset_n)|-> (ifu_rd_req == 0 && ifu_rd_addr == 0 && pdp_mem_opcode === '{0,0,0,0,0,0,9'bz} && pdp_op7_opcode === '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0});
endproperty

assert property(R2)
		//$display("Rule 2 passed");
		else $error("@ %d nsRule 2 Fail, pdp_op7_opcode = %p, pdp_mem_opcode = %p",$time, pdp_op7_opcode,pdp_mem_opcode);

C2: cover property(R2);

`endif




// ifu_rd_req should never be asserted high when stall is high(corner case)
`ifndef DISABLE_RULE3

property R3;
	@(posedge clk) stall |-> (!ifu_rd_req);
endproperty

assert property(R3)
		//$display("Rule 3 passed");
		else $error("Rule 3 Failed");

C3: cover property(R3);

`endif




// When stall is high, values on outputs ifu_rd_addr, pdp_mem_opcode and pdp_op7_opcode shouldn't change.
`ifndef DISABLE_RULE4

//assert property(@(posedge clk) (stall == 1'b1) |-> $stable(pdp_mem_opcode))
//		$display("@ %d nsRule 4 passed",$time);
//		else //$error("@ %d ns Rule 4 Failed",$time);
//			$error("@ %d nsRule 4 Fail, pdp_mem_opcode = %o",$time,pdp_mem_opcode);	

always_ff @(posedge clk)
begin
	if(stall == 1'b1 && reset_n && !flag)begin
		assert ((temp_pdp_mem_opcode === pdp_mem_opcode) && (temp_pdp_op7_opcode === pdp_op7_opcode))
		//$display("@%dns Rule 4 passed",$time);
		else $error("@ %d nsRule 4 Fail, temp_pdp_op7_opcode = %p, pdp_op7_opcode = %p",$time, temp_pdp_op7_opcode,pdp_op7_opcode);
	end
end



always @(posedge clk)begin
	if(!reset_n && stall)begin
		flag = 1'b1;
	end
	else if(flag == 1'b1)begin
		repeat(1)@(posedge clk);flag = 1'b0;
	end
end
	
`endif


always_ff @(posedge stall)begin
		temp_pdp_mem_opcode = pdp_mem_opcode;
		temp_pdp_op7_opcode = pdp_op7_opcode;
end



//When ifu_rd_req is asserted, then PC_value and ifu_rd_addr should be same.
`ifndef DISABLE_RULE5

property R5;
	@(posedge clk) $rose(ifu_rd_req)|-> (PC_value == ifu_rd_addr);
endproperty

assert property(R5)
		//$display("Rule 5 passed");
		else $error("Rule 5 Failed");

C5: cover property(R5);

`endif




//  After reset is asserted low to high, the ifu_rd_addr should set to base_addr after one clock cycle
`ifndef DISABLE_RULE6

property R6;
	@(posedge clk) $rose(reset_n)|-> ##1 (ifu_rd_addr == base_addr);
endproperty

assert property(R6)
		//$display("Rule 6 passed");
		else $error("Rule 6 Failed");

C6: cover property(R6);

`endif




//After ifu_rd_req is asserted low to high , the decoded values should be present on either pdp_mem_opcode or pdp_op7_opcode in the second clock cycle
`ifndef DISABLE_RULE7

property R7;
	@(posedge clk) $rose(ifu_rd_req)|-> ##2 new_mem_opcode && new_op7_opcode;
endproperty

assert property(R7)
		//$display("Rule 7 passed");
		else $error("Rule 7 Failed");

C7: cover property(R7);

`endif




//When an unsupported instruction is issued, pdp_mem_opcode = '{0,0,0,0,0,0,9'bz} and pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}.
`ifndef DISABLE_RULE8

property R8;
	@(posedge clk) $rose(ifu_rd_req) |-> ##2 unsupported == new_opcode1;
endproperty

assert property(R8)
		//$display("Rule 8 passed");
		else $error("Rule 8 Failed");

C8: cover property(R8);

`endif




//When PC_value and ifu_rd_addr matches with the base address for the first time, pdp_mem_opcode = '{0,0,0,0,0,0,9'bz} and pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}.
`ifndef DISABLE_RULE9

property R9;
	@(posedge clk) $fell(first_instruction) |-> ##0  pdp_mem_opcode === '{0,0,0,0,0,0,9'bz} && pdp_op7_opcode === '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} ;
endproperty

assert property(R9)
		//$display("@%d ns Rule 9 passed", $time);
		else $error("@%d ns Rule 9 Failed",$time);

C9: cover property(R9);

`endif





//After program starts, when the PC_value is octal 200 for the second time i.e. after the last instruction is executed, the ifu_rd_req should not be asserted high.
`ifndef DISABLE_RULE10

property R10;
	@(posedge clk)  $rose(last_instruction) |-> ##0 (!ifu_rd_req);
endproperty

assert property(R10)
		//$display("@%dns Rule 10 passed",$time);
		else $error("@%dns Rule 10 Failed",$time);

C10: cover property(R10);

`endif



//int_rd_req should be high only for one clock cycle.
`ifndef DISABLE_RULE11

property R11;
	@(posedge clk) $rose(ifu_rd_req) |-> ##[1:$] (!ifu_rd_req);
endproperty

assert property(R11)
		//$display("Rule 11 passed");
		else $error("Rule 11 Failed");

C11: cover property(R11);

`endif


//pdp_mem_opcode and pdp_op7_opcode shouldn?t set more than one instruction at a time.
`ifndef DISABLE_RULE12

property R12;
	@(posedge clk) $rose(stall)|-> ##2 flag_f1;
endproperty

assert property(R12)
		//$display("Rule 12 passed");
		else $error("Rule 12 Failed");

C12: cover property(R12);

`endif


always_comb begin
	if(reset_n == CLEAR)begin
		first_instruction = SET;
		last_instruction = CLEAR;
	end
	else if(ifu_rd_addr == `START_ADDRESS) begin
		if(first_instruction == SET) first_instruction = CLEAR;
		else last_instruction = SET;
	end
	else begin
		;//just waiting for the base address for the second time.
	end	
end



always @(negedge ifu_rd_req)begin
repeat(1) @(negedge clk);
decoded;
end

task decoded;
	A = '{0,0,0,0,0,0,12'hz};
	B = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	int_op_mem = A;
	int_op7 = B;
	unsupported = 1'b0;

                    if (ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] < 6) begin
                       case (ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3])
                          `AND: int_op_mem.AND = SET;
                          `TAD: int_op_mem.TAD = SET;
                          `ISZ: int_op_mem.ISZ = SET;
                          `DCA: int_op_mem.DCA = SET;
                          `JMS: int_op_mem.JMS = SET;
                          `JMP: int_op_mem.JMP = SET;
                          default: int_op_mem = A;
                       endcase
 
                    end else if (ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == 7) begin
                       case (ifu_rd_data)
                          `NOP    : int_op7.NOP = SET;
                          `IAC    : int_op7.IAC = SET;
                          `RAL    : int_op7.RAL = SET;
                          `RTL    : int_op7.RTL = SET;
                          `RAR    : int_op7.RAR = SET;
                          `RTR    : int_op7.RTR = SET;
                          `CML    : int_op7.CML = SET;
                          `CMA    : int_op7.CMA = SET;
                          `CIA    : int_op7.CIA = SET;
                          `CLL    : int_op7.CLL = SET;
                          `CLA1   : int_op7.CLA1 = SET;
                          `CLA_CLL: int_op7.CLA_CLL = SET;
                          `HLT    : int_op7.HLT = SET;
                          `OSR    : int_op7.OSR = SET;
                          `SKP    : int_op7.SKP = SET;
                          `SNL    : int_op7.SNL = SET;
                          `SZL    : int_op7.SZL = SET;
                          `SZA    : int_op7.SZA = SET;
                          `SNA    : int_op7.SNA = SET;
                          `SMA    : int_op7.SMA = SET;
                          `SPA    : int_op7.SPA = SET;
                          `CLA2   : int_op7.CLA2 = SET;
                          default : int_op7.NOP = SET;
                       endcase
		  end else
                         int_op7.NOP = SET;

   unsupported = !( 
   ifu_rd_data == `IAC ||
   ifu_rd_data == `RAL ||
   ifu_rd_data == `RTL ||
   ifu_rd_data == `RAR ||
   ifu_rd_data == `RTR ||
   ifu_rd_data == `CML ||
   ifu_rd_data == `CMA ||
   ifu_rd_data == `CIA ||
   ifu_rd_data == `CLL ||
   ifu_rd_data == `CLA1 ||
   ifu_rd_data == `CLA_CLL ||
   ifu_rd_data == `HLT ||
   ifu_rd_data == `OSR ||
   ifu_rd_data == `SKP ||
   ifu_rd_data == `SNL ||
   ifu_rd_data == `SZL ||
   ifu_rd_data == `SZA ||
   ifu_rd_data == `SNA ||
   ifu_rd_data == `SMA ||
   ifu_rd_data == `SPA ||
   ifu_rd_data == `CLA2 ||
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] < 6 ||
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `AND ||
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `TAD || 
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `ISZ ||
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `DCA || 
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `JMS || 
   ifu_rd_data[`DATA_WIDTH-1:`DATA_WIDTH-3] == `JMP);

endtask

always_comb
begin

    opcode_count =   (      temp_pdp_mem_opcode.AND +
                            temp_pdp_mem_opcode.TAD +
                            temp_pdp_mem_opcode.ISZ +
                            temp_pdp_mem_opcode.DCA +
                            temp_pdp_mem_opcode.JMS +
                            temp_pdp_mem_opcode.JMP +
			    temp_pdp_op7_opcode.IAC +
                            temp_pdp_op7_opcode.RAL +
                            temp_pdp_op7_opcode.NOP +
                            temp_pdp_op7_opcode.RTL +
                            temp_pdp_op7_opcode.RAR +
                            temp_pdp_op7_opcode.RTR +
                            temp_pdp_op7_opcode.CML +
                            temp_pdp_op7_opcode.CMA +
                            temp_pdp_op7_opcode.CIA +
                            temp_pdp_op7_opcode.CLL +
                            temp_pdp_op7_opcode.CLA1 +
                            temp_pdp_op7_opcode.CLA_CLL +
                            temp_pdp_op7_opcode.HLT +
                            temp_pdp_op7_opcode.OSR +
                            temp_pdp_op7_opcode.SKP +
                            temp_pdp_op7_opcode.SNL +
                            temp_pdp_op7_opcode.SZL +
                            temp_pdp_op7_opcode.SZA +
                            temp_pdp_op7_opcode.SNA +
                            temp_pdp_op7_opcode.SMA +
                            temp_pdp_op7_opcode.SPA +
                            temp_pdp_op7_opcode.CLA2 );

	if(opcode_count === 1) flag_f1 = SET;
	else flag_f1 = CLEAR;

end

   assign new_mem_opcode =  ((pdp_mem_opcode.AND ==  int_op_mem.AND)&&
                            (pdp_mem_opcode.TAD ==  int_op_mem.TAD)&&
                            (pdp_mem_opcode.ISZ ==  int_op_mem.ISZ)&&
                            (pdp_mem_opcode.DCA ==  int_op_mem.DCA)&&
                            (pdp_mem_opcode.JMS ==  int_op_mem.JMS)&&
                            (pdp_mem_opcode.JMP ==  int_op_mem.JMP));

   assign new_op7_opcode =  ((pdp_op7_opcode.NOP == int_op7.NOP) &&
                            (pdp_op7_opcode.IAC == int_op7.IAC) &&
                            (pdp_op7_opcode.RAL == int_op7.RAL) &&
                            (pdp_op7_opcode.RTL == int_op7.RTL) &&
                            (pdp_op7_opcode.RAR == int_op7.RAR) &&
                            (pdp_op7_opcode.RTR == int_op7.RTR) &&
                            (pdp_op7_opcode.CML == int_op7.CML) &&
                            (pdp_op7_opcode.CMA == int_op7.CMA) &&
                            (pdp_op7_opcode.CIA == int_op7.CIA) &&
                            (pdp_op7_opcode.CLL == int_op7.CLL) &&
                            (pdp_op7_opcode.CLA1 == int_op7.CLA1) &&
                            (pdp_op7_opcode.CLA_CLL == int_op7.CLA_CLL) &&
                            (pdp_op7_opcode.HLT == int_op7.HLT) &&
                            (pdp_op7_opcode.OSR == int_op7.OSR) &&
                            (pdp_op7_opcode.SKP == int_op7.SKP) &&
                            (pdp_op7_opcode.SNL == int_op7.SNL) &&
                            (pdp_op7_opcode.SZL == int_op7.SZL) &&
                            (pdp_op7_opcode.SZA == int_op7.SZA) &&
                            (pdp_op7_opcode.SNA == int_op7.SNA) &&
                            (pdp_op7_opcode.SMA == int_op7.SMA) &&
                            (pdp_op7_opcode.SPA == int_op7.SPA) &&
                            (pdp_op7_opcode.CLA2 == int_op7.CLA2));

   assign new_opcode1 =   !(pdp_mem_opcode.AND ||
                            pdp_mem_opcode.TAD ||
                            pdp_mem_opcode.ISZ ||
                            pdp_mem_opcode.DCA ||
                            pdp_mem_opcode.JMS ||
                            pdp_mem_opcode.JMP ||
			    pdp_op7_opcode.IAC ||
                            pdp_op7_opcode.RAL ||
                            pdp_op7_opcode.RTL ||
                            pdp_op7_opcode.RAR ||
                            pdp_op7_opcode.RTR ||
                            pdp_op7_opcode.CML ||
                            pdp_op7_opcode.CMA ||
                            pdp_op7_opcode.CIA ||
                            pdp_op7_opcode.CLL ||
                            pdp_op7_opcode.CLA1 ||
                            pdp_op7_opcode.CLA_CLL ||
                            pdp_op7_opcode.HLT ||
                            pdp_op7_opcode.OSR ||
                            pdp_op7_opcode.SKP ||
                            pdp_op7_opcode.SNL ||
                            pdp_op7_opcode.SZL ||
                            pdp_op7_opcode.SZA ||
                            pdp_op7_opcode.SNA ||
                            pdp_op7_opcode.SMA ||
                            pdp_op7_opcode.SPA ||
                            pdp_op7_opcode.CLA2 );

endmodule


