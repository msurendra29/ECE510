
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
//   Created by:   Bharath Reddy Godi
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================

import pdp8_pkg::*; // Importing contents from package pdp8_pkg
`include "pdp8_pkg.sv"
`include "instr_exec.sv"

module exe_checker
  (
   // From clkgen_driver module
   input clk,                              // Free running clock
   input reset_n,                          // Active low reset signal

   // From instr_decode unit to exec unit
   input [`ADDR_WIDTH-1:0] base_addr,      // Address for first instruction
   input pdp_mem_opcode_s pdp_mem_opcode,  // Decoded signals for memory instructions
   input pdp_op7_opcode_s pdp_op7_opcode,  // Decoded signals for op7 instructions

   // To instr_decode unit from exe unit
   output                   stall,         // Signal to stall instruction decoder
   output [`ADDR_WIDTH-1:0] PC_value,      // Current value of Program Counter

   // To memory_pdp unit from exe unit
   output                    exec_wr_req,  // Write request to memory
   output  [`ADDR_WIDTH-1:0] exec_wr_addr, // Write address 
   output  [`DATA_WIDTH-1:0] exec_wr_data, // Write data to memory
   output                    exec_rd_req,  // Read request to memory
   output  [`ADDR_WIDTH-1:0] exec_rd_addr, // Read address

   // From memory_pdp unit to exe unit
   input   [`DATA_WIDTH-1:0] exec_rd_data  // Read data returned by memory

   );

parameter BASE_ADDRESS = 12'o200,
SET = 1'b1,
CLEAR = 1'b0,
CLEAR_DATA = 12'd0;
time current_time;
reg[`ADDR_WIDTH-1:0] temp_PC, temp_PC2,wr_data;
reg supported,flag_f1,ISZ_flag;
reg [31:0] opcode_count;
wire rd_mem_opcode,wr_mem_opcode;
pdp_mem_opcode_s temp_pdp_mem_opcode;
pdp_op7_opcode_s temp_pdp_op7_opcode;

// Rule1: exec_rd_req and exec_wr_req shouldn?t be high at same time.
`ifndef DISABLE_RULE1
always @(posedge exec_wr_req or posedge exec_rd_req)
begin
assert (exec_wr_req !== exec_rd_req)
		//$display("Rule 1 passed");
		else $error("Rule 1 Failed");
end
`endif

//Rule2: If exec_rd_req or exec_wr_req is high, then stall should be high.
`ifndef DISABLE_RULE2

property R2;

	@(posedge clk) ($rose(exec_rd_req) ||  $rose(exec_wr_req)) |-> stall === SET;

endproperty

assert property(R2)
		//$display("Rule 2 passed");
		else $error("Rule 2 Failed");

C2: cover property(R2);

`endif

//3.	When stall fell, PC value should be updated in the same cycle
`ifndef DISABLE_RULE3

property R3;

	@(posedge clk) disable iff (temp_pdp_mem_opcode.ISZ) $fell(stall) |-> PC_value == temp_PC;

endproperty

assert property(R3)
		//$display("Rule 3 passed");
		else $error("Rule 3 Failed PC = %o temp_PC = %o",PC_value, temp_PC);

C3: cover property(R3);

`endif


//4A: int_exec_rd_addr should be equal to pdp_mem_opcode.mem_inst_addr during instructions AND, TAD, ISZ instructions. (hint: when exec_rd_req = 1 we need to check address pin).
`ifndef DISABLE_RULE4A

property R4A;

	@(posedge clk) ($rose(exec_rd_req)) |-> (rd_mem_opcode) && (exec_rd_addr === temp_pdp_mem_opcode.mem_inst_addr);

endproperty

assert property(R4A) 
		//$display("Rule 4A passed");
		else $error("Rule 4A Failed  %d pdp_mem_opcode.mem_inst_addr = %d",rd_mem_opcode,temp_pdp_mem_opcode.mem_inst_addr);

C4A: cover property(R4A);

`endif

//4B: int_exec_wr_addr should be equal to pdp_mem_opcode.mem_inst_addr during instructions DCA JMS, ISZ instructions. (hint: when exec_wr_req = 1 we need to check address pin).
`ifndef DISABLE_RULE4B

property R4B;

	@(posedge clk) ($rose(exec_wr_req)) |-> (wr_mem_opcode) && (exec_wr_addr === temp_pdp_mem_opcode.mem_inst_addr);

endproperty


assert property(R4B) 
		//$display("Rule 4B passed");
		else $error("Rule 4B Failed  %d pdp_mem_opcode.mem_inst_addr = %d",wr_mem_opcode,temp_pdp_mem_opcode.mem_inst_addr);

C4B: cover property(R4B);

`endif

//REMOVED
////5. When AND, TAD, ISZ instructions are on pdp_mem_opcode, exec_rd_req should be high on within 3 clock cycle, after stall is set to high.
//`ifndef DISABLE_RULE5
//assert property(@(posedge clk) disable iff (!reset_n) (rd_mem_opcode && $rose(stall)) |-> ##[1:3] exec_rd_req)
//		$display("Rule 5 passed");
//		else $error("Rule 5 Failed ");
//`endif
//
//REMOVED
////6. When DCA, JMS, ISZ instructions are on pdp_mem_opcode, exec_wr_req should be high on within 7 clock cycle, after stall is set to high.
//`ifndef DISABLE_RULE6
//assert property(@(posedge clk) disable iff (!reset_n) (wr_mem_opcode && $rose(stall)) |-> ##[1:7] exec_wr_req)
//		$display("Rule 6 passed");
//		else $error("Rule 6 Failed ");
//`endif



//10.	ISZ:  PC_value should be incremented by 2, when the content of memory location is zero after incremented
`ifndef DISABLE_RULE10

property R10;

	@(posedge clk) ($fell(stall) && temp_pdp_mem_opcode.ISZ)|-> temp_PC2 == PC_value;

endproperty

assert property (R10)
		//$display("Rule 10 passed");
		else $error("Rule 10 Failed");

C10: cover property(R10);

`endif


//REMOVED
////14. int_exec_wr_addr should be pdp_mem_opcode.mem_inst_addr, when int_exec_wr_req ==1.
//`ifndef DISABLE_RULE14
//assert property(@(posedge clk) temp_pdp_mem_opcode.JMS && flag_f1 && $rose(exec_wr_req) |-> exec_wr_addr == temp_pdp_mem_opcode.mem_inst_addr)
//		$display("Rule 14 passed");
//		else $error("Rule 14 Failed ");
//`endif


//20A. JMS instruction should expect exec_wr_req.
`ifndef DISABLE_RULE20A

property R20A;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.JMS && $rose(stall) |-> ##[1:7]exec_wr_req;

endproperty

assert property(R20A)
		//$display("Rule 20A passed");
		else $error("Rule 20A Failed ");

C20A: cover property(R20A);

`endif

//20B. JMS instruction should expect exec_wr_req.
`ifndef DISABLE_RULE20B

property R20B;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.DCA && $rose(stall) |-> ##[1:7]exec_wr_req;

endproperty

assert property(R20B)
		//$display("Rule 20B passed");
		else $error("Rule 20B Failed ");

C20B: cover property(R20B);
`endif

//20C. ISZ instruction should expect exec_wr_req.
`ifndef DISABLE_RULE20C

property R20C;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.ISZ && $rose(stall) |-> ##[1:7]exec_wr_req;

endproperty

assert property(R20C)
		//$display("Rule 20C passed");
		else $error("Rule 20C Failed ");

C20C: cover property(R20C);

`endif

//20D. AND instruction should expect exec_rd_req.
`ifndef DISABLE_RULE20D

property R20D;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.AND && $rose(stall) |-> ##[1:3]exec_rd_req;

endproperty

assert property(R20D)
		//$display("Rule 20D passed");
		else $error("Rule 20D Failed ");

C20D: cover property(R20D);
`endif

//20E. ISZ instruction should expect exec_rd_req.
`ifndef DISABLE_RULE20E

property R20E;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.ISZ && $rose(stall) |-> ##[1:3]exec_rd_req;

endproperty

assert property(R20E)
		//$display("Rule 20E passed");
		else $error("Rule 20E Failed ");

C20E: cover property(R20E);

`endif

//20F. TAD instruction should expect exec_rd_req.
`ifndef DISABLE_RULE20F

property R20F;

	@(posedge clk) disable iff (!reset_n) temp_pdp_mem_opcode.TAD && $rose(stall) |-> ##[1:3]exec_rd_req;

endproperty


assert property(R20F)
		//$display("Rule 20F passed");
		else $error("Rule 20F Failed ");

C20F: cover property(R20F);

`endif

//REMOVED
////15.	JMS: PC value should be pdp_mem_opcode.mem_inst_addr+1 by the end of instruction.($fell(stall)).
//`ifndef DISABLE_RULE15
//assert property(@(posedge clk) (temp_pdp_mem_opcode.JMS && flag_f1 && $fell(stall)) |-> PC_value === temp_pdp_mem_opcode.mem_inst_addr+1)
//		$display("Rule 15 passed");
//		else $error("Rule 15 Failed ");
//`endif




//16.	JMS: exec_wr_data should be PC+1(following instruction) value when exec_wr_req is high.
`ifndef DISABLE_RULE16

property R16;

	@(posedge clk) temp_pdp_mem_opcode.JMS && $rose(exec_wr_req) |-> exec_wr_data === wr_data;

endproperty

assert property(R16)
		//$display("Rule 16 passed");
		else $error("Rule 16 Failed");

C16: cover property(R16);

`endif


//REMOVED
////17.JMP: PC value should be pdp_mem_opcode.mem_inst_addr by the end of instruction.($fell(stall)).
//`ifndef DISABLE_RULE17
//assert property(@(posedge clk) (temp_pdp_mem_opcode.JMP && flag_f1 && $fell(stall)) |-> PC_value === temp_pdp_mem_opcode.mem_inst_addr)
//		$display("Rule 17 passed");
//		else $error("Rule 17 Failed");
//`endif



//18.	Extra. When reset_n is low, PC value should be base address.
`ifndef DISABLE_RULE18

property R18;

	@(posedge clk)  $fell(reset_n) |-> PC_value === base_addr;

endproperty

assert property(R18)
		//$display("Rule 18 passed");
		else $error("Rule 18 Failed");

C18: cover property(R18);

`endif

assign rd_mem_opcode = ( pdp_mem_opcode.AND ||  pdp_mem_opcode.TAD || pdp_mem_opcode.ISZ );
assign wr_mem_opcode = ( pdp_mem_opcode.DCA || pdp_mem_opcode.JMS || pdp_mem_opcode.ISZ );

always_ff @(posedge stall) begin	//For Rule 3

		temp_PC = PC_value;
		if(pdp_mem_opcode.JMS == SET)begin wr_data = temp_PC + 1; temp_PC = pdp_mem_opcode.mem_inst_addr + 1 ;end
		else if(pdp_mem_opcode.JMP == SET)  temp_PC = pdp_mem_opcode.mem_inst_addr;
		else temp_PC = temp_PC + 1;
		temp_pdp_mem_opcode = pdp_mem_opcode;
		temp_pdp_op7_opcode = pdp_op7_opcode;	
		temp_PC2 = PC_value;

end

always_ff @(posedge exec_wr_req)begin	//For Rule 10 ISZ

	if(exec_wr_data == CLEAR_DATA)
		temp_PC2 = temp_PC2+2;
	else temp_PC2 = temp_PC2+1;
end

always_ff @(posedge reset_n)
begin
	temp_PC = BASE_ADDRESS;
	temp_PC2 = BASE_ADDRESS;
end





//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
//
//				Coverage Bins
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------



   covergroup supported_opcodes @(posedge stall);

	mem_AND: coverpoint pdp_mem_opcode.AND{
			bins AND = {1};}

	mem_TAD: coverpoint pdp_mem_opcode.TAD{
			bins TAD = {1};}

	mem_ISZ: coverpoint pdp_mem_opcode.ISZ{
			bins ISZ = {1};}

	mem_DCA: coverpoint pdp_mem_opcode.DCA{
			bins DCA = {1};}

	mem_JMS: coverpoint pdp_mem_opcode.JMS{
			bins JMS = {1};}

	mem_JMP: coverpoint pdp_mem_opcode.JMP{
			bins JMP = {1};}

	op7_CLA_CLL: coverpoint pdp_op7_opcode.CLA_CLL{
			bins CLA_CLL = {1};}

	op7_NOP: coverpoint pdp_op7_opcode.NOP{
			bins NOP = {1};}

   endgroup

   covergroup unsupported_opcodes @(posedge stall);

	op7_IAC: coverpoint pdp_op7_opcode.IAC{
			bins IAC = {1};}

	op7_RAL: coverpoint pdp_op7_opcode.RAL{
			bins RAL = {1};}

	op7_RTL: coverpoint pdp_op7_opcode.RTL{
			bins RTL = {1};}

	op7_RAR: coverpoint pdp_op7_opcode.RAR{
			bins RAR = {1};}

	op7_RTR: coverpoint pdp_op7_opcode.RTR{
			bins RTR = {1};}

	op7_CML: coverpoint pdp_op7_opcode.CML{
			bins CML = {1};}

	op7_CMA: coverpoint pdp_op7_opcode.CMA{
			bins CMA = {1};}

	op7_CLL: coverpoint pdp_op7_opcode.CLL{
			bins CLL = {1};}

	op7_CLA1: coverpoint pdp_op7_opcode.CLA1{
			bins CLA1 = {1};}

	op7_HLT: coverpoint pdp_op7_opcode.HLT{
			bins HLT = {1};}

	op7_OSR: coverpoint pdp_op7_opcode.OSR{
			bins OSR = {1};}

	op7_SKP: coverpoint pdp_op7_opcode.SKP{
			bins SKP = {1};}

	op7_SNL: coverpoint pdp_op7_opcode.SNL{
			bins SNL = {1};}

	op7_SZL: coverpoint pdp_op7_opcode.SZL{
			bins SZL = {1};}

	op7_SZA: coverpoint pdp_op7_opcode.SZA{
			bins SZA = {1};}

	op7_SNA: coverpoint pdp_op7_opcode.SNA{
			bins SNA = {1};}

	op7_SMA: coverpoint pdp_op7_opcode.SMA{
			bins SMA = {1};}

	op7_SPA: coverpoint pdp_op7_opcode.SPA{
			bins SPA = {1};}

	op7_CLA2: coverpoint pdp_op7_opcode.CLA2{
			bins CLA2 = {1};}

   endgroup


	supported_opcodes supported_inst = new();
	unsupported_opcodes unsupported_inst = new();


// Corner Case 2
property corner_case2;

	@(posedge clk) disable iff (!reset_n) (pdp_mem_opcode.ISZ && (exec_rd_data === 12'o7777 || exec_rd_data === 12'o0000)) |-> SET;

endproperty

CC1: cover property(corner_case2);





endmodule



//----------------------------------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------
//						Interface for White Box Testing
//----------------------------------------------------------------------------------------------------------------
//----------------------------------------------------------------------------------------------------------------


interface exec_in_check (input reg intLink, 
			 input reg [`DATA_WIDTH:0] intAcc, 
			 input [`DATA_WIDTH-1:0] exec_rd_data,
			 input [`DATA_WIDTH-1:0] exec_wr_data,
			 input [`DATA_WIDTH-1:0] exec_wr_addr,
			 input exec_wr_req,
			 input exec_rd_req,
			 input pdp_mem_opcode_s pdp_mem_opcode,
                         input pdp_op7_opcode_s pdp_op7_opcode,
			 input [`ADDR_WIDTH-1:0] PC_value,
			 input stall,
			 input clk);

reg [31:0] opcode_count;
reg temp_link, flag_f1;
reg [`ADDR_WIDTH-1:0] temp_PC_value;
reg [`DATA_WIDTH:0]temp_Acc;
reg [`DATA_WIDTH:0]Acc;
pdp_mem_opcode_s temp_pdp_mem_opcode;
pdp_op7_opcode_s temp_pdp_op7_opcode;

parameter BASE_ADDRESS = 12'o200,
SET = 1'b1,
CLEAR = 1'b0,
CLEAR_DATA = 12'd0;


always_comb begin

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

always @(posedge stall)begin

	temp_link = intLink;
	temp_pdp_mem_opcode = pdp_mem_opcode;
	temp_pdp_op7_opcode = pdp_op7_opcode;
	temp_PC_value = PC_value;
	temp_Acc = intAcc;
end

always @(negedge exec_rd_req)begin
	execution;
end

task execution;
	Acc = intAcc;
	Acc[`DATA_WIDTH] = CLEAR;
	if(temp_pdp_mem_opcode.AND)begin
		temp_Acc = Acc & exec_rd_data;
	end

	else if(temp_pdp_mem_opcode.TAD)begin
		temp_Acc = Acc + exec_rd_data;
		if(temp_Acc[`DATA_WIDTH])begin
			temp_link = ~temp_link;
			
		end
	end

endtask


//7.	AND:  AC <- AC & int_exec_rd_data, when stall is high.
`ifndef DISABLE_RULE7

property R7;

	@(posedge clk) $fell(stall) &&  temp_pdp_mem_opcode.AND |-> temp_Acc == intAcc;

endproperty

assert property (R7) //[11:0]temp_Acc.
		//$display("Rule 7 passed");
		else $error("Rule 7 Failed");

C7: cover property(R7);

`endif

//8.	TAD:  AC <- AC + int_exec_rd_data, when stall is high. Link <- ~Link, when stall fell and pdp_mem_opcode_mem is TAD.
`ifndef DISABLE_RULE8

property R8;

	@(posedge clk) $fell(stall) &&  temp_pdp_mem_opcode.TAD |-> (temp_Acc === intAcc) && (temp_link == intLink);

endproperty

assert property (R8)
		//$display("Rule 8 passed");
		else $error("Rule 8 Failed");

C8: cover property(R8);

`endif

//11.	White BOX: CLA_CLL:  Accumulator and link, should be cleared by the end of the instruction CLA_CLL.
`ifndef DISABLE_RULE11

property R11;

	@(posedge clk) $fell(stall) && temp_pdp_op7_opcode.CLA_CLL |-> (intAcc === CLEAR_DATA) && (intLink == CLEAR);

endproperty


assert property (R11)
		//$display("Rule 11 passed");
		else $error("Rule 11 Failed");

C11: cover property(R11); 

`endif

//12: DCA:  when exec_wr_req is high, exec_wr_data should be equal to accumulator value
`ifndef DISABLE_RULE12

property R12;

	@(posedge clk) $rose(exec_wr_req) && temp_pdp_mem_opcode.DCA |-> exec_wr_data == temp_Acc[11:0];

endproperty


assert property (R12)
		//$display("Rule 12 passed");
		else $error("Rule 12 Failed");

C12: cover property(R12); 

`endif

//13: DCA: Accumulator should be cleared by the end of instruction.( When stall fell)
`ifndef DISABLE_RULE13

property R13;

	@(posedge clk) $fell(stall) && temp_pdp_mem_opcode.DCA |-> intAcc == CLEAR_DATA;

endproperty
assert property (R13)
		//$display("Rule 13 passed");
		else $error("Rule 13 Failed");

C13: cover property(R13); 


`endif

// Corner Case 1
property corner_case1;
	@(posedge clk)(intAcc[`DATA_WIDTH] == SET);
endproperty

CC2: cover property(corner_case1);



endinterface

bind instr_exec exec_in_check F1(.*);
