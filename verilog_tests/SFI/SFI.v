`timescale 1ns / 1ps

//SFI Testing verilog code

module SFI(ri, ro);
	output [31:0] ro;
	reg [31:0] ro;
	input [31:0] ri;
	
	always @(*)
	begin
	 	ro = 0;
		if (~(((ri >> 22) & (4294967295 >> 4294967241)) ^ 162))begin
			ro = ri;
		end
		else begin
		end
	end
endmodule
