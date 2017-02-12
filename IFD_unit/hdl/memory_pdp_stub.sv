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
//   Filename:     memory_pdp.sv
//   Description:  
//   Created by:   Surendra Madula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================
import pdp8_pkg::*;
`include "pdp8_pkg.sv"

module memory_pdp_stub
  (
   // Global input
   input clk,

   input                    ifu_rd_req,
   input  [`ADDR_WIDTH-1:0] ifu_rd_addr,
   output [`DATA_WIDTH-1:0] ifu_rd_data

   );

   reg [11:0] array[21:0];
   reg [`DATA_WIDTH-1:0] int_ifu_rd_data, ran1;
   integer i;

initial begin

   array = '{`NOP,`HLT,`CLL,`CLA1,`CLA_CLL,`CLA2,`IAC,`RAL,`RTL,`RAR,`RTR,`CML,`CMA,`CIA,`OSR,`SKP,`SNL,`SZL,`SZA,`SNA,`SMA,`SPA};
   int_ifu_rd_data = {`DATA_WIDTH{1'b0}};
   i = 0;


   repeat (10000)@(posedge ifu_rd_req)begin

	repeat(1)@(posedge clk);
	if(i <= 21)begin
		ran1 = array[i];
		i = i+1;
	end
	else begin
		ran1 = $urandom_range(4096);
	end

	$display("@%2d %o",$time,ran1);
	int_ifu_rd_data = ran1;

   end
   
end

   // Continuous assignment to output
   assign ifu_rd_data = int_ifu_rd_data;


endmodule // memory_pdp