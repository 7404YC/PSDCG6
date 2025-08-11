class spi_drv extends uvm_driver #(spi_tran);

	`uvm_component_utils(spi_drv)

	uvm_analysis_port # (spi_tran) drv_ap = new("drv_ap", this);

	virtual spi_ctrl_if vif;

	function new(name, uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if (!uvm_config_db # (virtual spi_if)::get(this, "", "vif", vif)) begin
			`uvm_error("DRIVER", "Virtual interface (drv_cb) not found in config db")
		end
	endfunction

	task run_phase(uvm_phase phase);
		
		spi_tran tr;
		
		forever begin

			seq_item_port.get_next_item(tr);
			drv_ap.write(tr);

			// TODO: Drive the signals from TB to DUT

			seq_item_port.item_done();

		end

	endtask

endclass
