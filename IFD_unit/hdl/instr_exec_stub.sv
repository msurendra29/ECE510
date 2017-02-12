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
//   Filename:     instr_exec_stub.sv
//   Description:  This module is a responder stub to the decoder
//   Created by:   Surendra Maddula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================

import pdp8_pkg::*;
`include "pdp8_pkg.sv"

module instr_exec_stub
  (
   // From clkgen_driver module
   input clk,                              // Free running clock
   input reset_n,                          // Active low reset signal

   // From instr_decode module
   input [`ADDR_WIDTH-1:0] base_addr,      // Address for first instruction
   input pdp_mem_opcode_s pdp_mem_opcode,  // Decoded signals for memory instructions
   input pdp_op7_opcode_s pdp_op7_opcode,  // Decoded signals for op7 instructions

   // To instr_decode module
   output                   stall,         // Signal to stall instruction decoder
   output [`ADDR_WIDTH-1:0] PC_value      // Current value of Program Counter


   );

   reg                   int_stall;
   reg [`ADDR_WIDTH-1:0] int_PC_value;
   reg			 toggle;
   reg                   new_mem_opcode; // Signal to detect a new memory instruction
   reg                   new_op7_opcode; // Signal to detect a new op7 instruction

   int counter = 0;


   parameter 
	SET = 1'b1,
	CLEAR = 1'b0;

   enum {IDLE,
         STALL,
         UNSTALL,
	 OPERATION,
	 DELAY   } current_state, next_state;





   assign new_mem_opcode = (pdp_mem_opcode.AND ||
                            pdp_mem_opcode.TAD ||
                            pdp_mem_opcode.ISZ ||
                            pdp_mem_opcode.DCA ||
                            pdp_mem_opcode.JMS ||
                            pdp_mem_opcode.JMP);

   assign new_op7_opcode = (pdp_op7_opcode.NOP ||
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
                            pdp_op7_opcode.CLA2);

initial begin
	toggle = CLEAR;
end

always @(posedge reset_n)begin
	repeat(2)@(posedge clk);
	toggle = ~toggle;
end


always_ff @(posedge clk or negedge reset_n) 
   if (!reset_n && toggle) current_state <= IDLE;
   else          current_state <= next_state;

always_comb begin

  case(current_state)

	IDLE: begin
		next_state = STALL;
		int_PC_value = `START_ADDRESS;
		int_stall = CLEAR;
	end

	STALL: begin

		if(pdp_mem_opcode === '{1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,12'hxxx} && pdp_op7_opcode === '{1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx,1'hx})begin
			int_stall = 1'bx;
		end
		else if(new_mem_opcode || new_op7_opcode)begin

			//$display("@%2d pdp_mem_opcode = %d",$time,pdp_mem_opcode.mem_inst_addr);
			//$display(" @%2d,pdp_mem_opcode %p,pdp_op7_opcode %p",$time,pdp_mem_opcode,pdp_op7_opcode);
			int_stall = SET;
			next_state = OPERATION;
		end
		
		//else int_stall = CLEAR;

	end

	OPERATION:begin
			if(counter == 4)
				next_state = UNSTALL;
			else
				next_state = OPERATION;
		  end


	UNSTALL: begin
		int_stall = CLEAR;
		int_PC_value = int_PC_value + 1;
		next_state = DELAY;
	end

	DELAY: begin
		next_state = STALL;
	end

  endcase
end

always_ff @(posedge clk)begin
	case(current_state)

		OPERATION: begin
				counter = counter + 1;

			   end
		DELAY: counter = 0;
	endcase
end


	assign stall = int_stall;
	assign PC_value = int_PC_value;

endmodule //  instr_exec
