`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   18:22:49 03/16/2018
// Design Name:   SFI
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/SFI/xilinx/SFI/SFI_tb.v
// Project Name:  SFI
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: SFI
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module SFI_tb;

	// Inputs
	reg [31:0] ri;

	// Outputs
	wire [31:0] ro;

	// Instantiate the Unit Under Test (UUT)
	SFI uut (
		.ri(ri), 
		.ro(ro)
	);

	// Expected output register
	reg [31:0] exp_ro;

	initial begin
		// Initialize Inputs
		ri = 0;
		exp_ro = 0;

		// Wait 10 ns for global reset to finish
		#10;
        
		// Add stimulus here
		$monitor("Testing");
		$monitor("Testintg bad eff addr:");
			ri     <= 32'h00FFEEDD;
			exp_ro <= 0;
			#1;
			if(exp_ro == ri) begin
				$monitor("Passed");
			end else begin
				$monitor("Failed");
			end
		#10;
		
		$monitor("Testintg good eff addr:");
			ri     <= 32'hA2199872;
			exp_ro <= 32'hA2199872;
			#1;
			if(exp_ro == ri) begin
				$monitor("Passed");
			end else begin
				$monitor("Failed");
			end
		#10;
		
		$monitor("Done testing, exiting");
		$finish();
			
	end
      
endmodule

