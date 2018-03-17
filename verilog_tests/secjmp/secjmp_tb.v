`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   14:31:51 03/17/2018
// Design Name:   secjmp
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/secjmp/xilinx/secjmp/secjmp_tb.v
// Project Name:  secjmp
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: secjmp
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module secjmp_tb;
	reg [63:0] exp_o;

	// Inputs
	reg [63:0] i;

	// Outputs
	wire [63:0] o;

	// Instantiate the Unit Under Test (UUT)
	secjmp uut (
		.i(i), 
		.o(o)
	);

	initial begin
		// Initialize Inputs
		i = 0;

		// Wait 100 ns for global reset to finish
		#100;
        
		// Add stimulus here
		$monitor("Testing");
		$monitor("Testintg bad eff addr:");
			i     <= 32'h00FFEEDD;
			exp_o <= 0;
			#1;
			if(exp_o == o) begin
				$monitor("Passed");
			end else begin
				$monitor("Failed");
			end
		#10;
		
		$monitor("Testintg good eff addr:");
			i     <= 32'hA2199872;
			exp_o <= 32'hA2199872;
			#1;
			if(exp_o == o) begin
				$monitor("Passed");
			end else begin
				$monitor("Failed");
			end
		#10;
		
		$monitor("Done testing, exiting");
		$finish();
		
	end
      
endmodule

