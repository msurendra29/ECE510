// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Instructor :  Tareque Ahmad
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     chip_sb.sv
//   Description:  Scoreboard to perform the end of test checking
//
//   Created by:   Bharath Reddy Godi
//   Date:         May 27, 2016
//
//   Copyright:    Surendra maddula, Bharath Reddy Godi
// =======================================================================

timeunit 1ns;
timeprecision 1ns;

// Import the package
import pdp8_pkg::*;
`include "pdp8_pkg.sv"
`include "instr_exec.sv"

`define OUT_ENDTEST "endtest.mem" 

module chip_sb(
		input clk,
		input reset_n,
		input ifu_rd_req,
		input [`ADDR_WIDTH-1:0] ifu_rd_addr,
		input [`DATA_WIDTH-1:0] ifu_rd_data,
		input exec_rd_req,
		input [`ADDR_WIDTH-1:0] exec_rd_addr,
		input [`DATA_WIDTH-1:0] exec_rd_data,
		input exec_wr_req,
		input [`ADDR_WIDTH-1:0] exec_wr_addr,
		input [`DATA_WIDTH-1:0] exec_wr_data,
   		input pdp_mem_opcode_s pdp_mem_opcode,  // Decoded signals for memory instructions
   		input pdp_op7_opcode_s pdp_op7_opcode  // Decoded signals for op7 instructions
		);

reg [2:0]opcode;
reg [2:0]inst;
reg [`ADDR_WIDTH-1:0] base_address, pc, instruction, address;
reg [`DATA_WIDTH-1:0]acc,temp_acc;
reg link;
reg [11:0] PDP_memory [0:4095];
reg [11:0] PDP_out_memory [0:4095];
reg first_instruction,last_instruction;

//-----checker 1 variables-----------
reg unsupported;
reg                   new_mem_opcode; // Signal to detect a new memory instruction
reg                   new_op7_opcode; // Signal to detect a new op7 instruction
pdp_mem_opcode_s A, int_op_mem, temp_pdp_mem_opcode;
pdp_op7_opcode_s B, int_op7,temp_pdp_op7_opcode;




parameter 	AND = 3'd0,
		TAD = 3'd1,
		ISZ = 3'd2,
		DCA = 3'd3,
		JMS = 3'd4,
		JMP = 3'd5,
		NOP = 3'd7,
		CLEAR = 1'b0,
		SET = 1'b1,
		CLEAR_DATA = 12'd0;
			

integer k;
integer file;
integer outfile, count;




//---------------------------------------------------------------------------------------------
//-----------------------------------End of Memory test----------------------------------------
//---------------------------------------------------------------------------------------------

always @(posedge exec_wr_req)begin

	PDP_out_memory[exec_wr_addr] = exec_wr_data;
	$display("PDP_out_memory[%o] , exec_wr_data = %o",exec_wr_addr,exec_wr_data);
	$display("PDP_memory[%o], exec_wr_data = %o",exec_wr_addr,PDP_memory[exec_wr_addr]);

end




`ifndef DISABLE_RULE4
assert property(@(posedge clk)  $rose(last_instruction) |-> PDP_out_memory === PDP_memory)
		$display("@%dns Passed End of memory test",$time);
		else $error("Failed End of memory test");
`endif


always_comb begin
	if(reset_n === CLEAR)begin
		first_instruction = SET;
		last_instruction = CLEAR;
	end
	else if(ifu_rd_addr === `START_ADDRESS) begin
		if(first_instruction === SET) first_instruction = CLEAR;
		else last_instruction = SET;
	end
	else begin
		;//just waiting for the base address for the second time.
	end	
end


always @(last_instruction)begin

	if((PDP_out_memory === PDP_memory)&& last_instruction)begin
		$display("@%dns Passed End of memory test",$time);
	end
	else if((PDP_out_memory !== PDP_memory)&& last_instruction) begin
		$error("Failed End of memory test");
	end

end



initial begin
	base_address = `START_ADDRESS;	
	pc = `START_ADDRESS;
	acc = CLEAR_DATA;
	temp_acc = CLEAR_DATA;
	address = CLEAR_DATA;
end



 initial begin
      for (k=0; k<4096; k=k+1)  begin
         //PDP_memory[k] = `DATA_WIDTH'bz;
         PDP_memory[k] = k;
	 PDP_out_memory[k] = k;
      end

      file = $fopen(`MEM_FILENAME, "r");
      if (file == 0)
         $display("\nError: Could not find file %s\n",`MEM_FILENAME);
      else begin
         $readmemh(`MEM_FILENAME,PDP_memory);
	 PDP_out_memory = PDP_memory;
      end

 end

always @(posedge reset_n)begin
	pdp8;
end

task pdp8;


$display("Task Execution for end of test check");

do begin
	instruction = PDP_memory[pc];
	opcode = instruction [`DATA_WIDTH-1:`DATA_WIDTH-3];
	address = instruction [`DATA_WIDTH-4:0];
	$display("instruction = %o, opcode = %o, address = %o",instruction,opcode,address);

	case(opcode)
		AND: begin acc = acc & PDP_memory[address];
				pc = pc + 1'o1; end

		TAD: begin acc = acc + PDP_memory[address];	
				pc = pc + 1'o1; end

		ISZ: begin PDP_memory[address] = PDP_memory[address] + 1'o1;

				if(PDP_memory[address] === CLEAR_DATA)
					pc = pc + 2'o2;
				else
					pc = pc + 1'o1;
		     end

		DCA: begin PDP_memory[address] = acc;
			   acc = CLEAR_DATA;
			   pc = pc + 1'o1;
		     end

		JMS: begin PDP_memory[address] = pc + 1'o1;
			   pc = address + 1'o1; end
		JMP: begin pc = address; end

		NOP:begin
			if(instruction === `CLA_CLL)begin
				acc = CLEAR_DATA;
				link = CLEAR;
				pc = pc + 1'o1;
			end
			else pc = pc + 1'o1;
		    end

		default: pc = pc + 1'o1;

	endcase
end
while(pc !== `START_ADDRESS);

//$display("PDP_memory = %p",PDP_memory);

endtask


//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
//
//				Coverage
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------




sequence x;
	@(posedge ifu_rd_req)
		##1(ifu_rd_data ==`CLA_CLL) ##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `TAD) ##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `TAD) ##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `DCA) ##[1:7](ifu_rd_data ==`HLT) ##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `JMP);
endsequence

BP: cover property (x);



sequence y;
	@(posedge ifu_rd_req)
		##1(ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `TAD) ##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `AND)##[1:7](ifu_rd_data [`DATA_WIDTH-1:`DATA_WIDTH-3] == `ISZ);
endsequence

BS: cover property (y);


covergroup scenario @(negedge ifu_rd_req);

	opcodes: coverpoint inst{
			ignore_bins ignore_opcode = {7};}

	NOP: coverpoint ifu_rd_data{
		bins NOP = {`NOP};
		bins HLT = {`HLT};
		bins CLL = {`CLL};
		bins CLA1 = {`CLA1};
		bins CLA_CLL = {`CLA_CLL};
		bins CLA2 = {`CLA2};
		bins IAC = {`IAC};
		bins RAL = {`RAL};
		bins RTL = {`RTL};
		bins RAR = {`RAR};
		bins RTR = {`RTR};
		bins CML = {`CML};
		bins CMA = {`CMA};
		bins CIA = {`CIA};
		bins OSR = {`OSR};
		bins SKP = {`SKP};
		bins SNL = {`SNL};
		bins SZL = {`SZL};
		bins SZA = {`SZA};
		bins SNA = {`SNA};
		bins SMA = {`SMA};
		bins SPA = {`SPA};
		bins other[1] = default; }

endgroup

scenario scenario_inst = new();

//final begin
//
//	outfile = $fopen(`OUT_FILENAME, "r");
//	if (outfile == 0)
//	   $display("\nError: Could not find file %s\n",`OUT_FILENAME);
//	else begin
//	   $readmemh(`OUT_FILENAME,PDP_out_memory);
//	   $display("PDP_out_memory = %p",PDP_out_memory);
//	end
//	
//	$fclose(outfile);
//
//	outfile = $fopen(`OUT_ENDTEST, "w");
//
//	if(PDP_out_memory === PDP_memory)begin
//		$display("Passed End of memory test");
//		$writememh(`OUT_ENDTEST,PDP_out_memory);
//	end
//	else begin
//		$error("Failed End of memory test");
//		$writememh(`OUT_ENDTEST,PDP_out_memory);
//	end
//
//end

endmodule


