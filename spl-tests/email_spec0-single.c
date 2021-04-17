// *** SELECTING FEATURES AND VALID PRODUCTS ***  //
#pragma merger(0,"featureselect.i","")


/* features int[0,1] __SELECTED_FEATURE_Keys;
features int[0,1] __SELECTED_FEATURE_Sign;
features int[0,1] __SELECTED_FEATURE_AddressBook;
features int[0,1] __SELECTED_FEATURE_Encrypt;
features int[0,1] __SELECTED_FEATURE_Decrypt;
features int[0,1] __SELECTED_FEATURE_Verify;  
features int[0,1] __SELECTED_FEATURE_AutoResponder;
features int[0,1] __SELECTED_FEATURE_Forward;  */


int __SELECTED_FEATURE_Base  ;
int __SELECTED_FEATURE_Keys  ;
int __SELECTED_FEATURE_Encrypt  ;
int __SELECTED_FEATURE_AutoResponder  ;
int __SELECTED_FEATURE_AddressBook  ;
int __SELECTED_FEATURE_Sign  ;
int __SELECTED_FEATURE_Forward  ;
int __SELECTED_FEATURE_Verify  ;
int __SELECTED_FEATURE_Decrypt  ;
int __GUIDSL_ROOT_PRODUCTION  ;
int select_one(void) ;
void select_features(void) ;
void select_helpers(void) ;

int select_one() { 
  int retValue_acc ;
  int choice = [0,1]; //__VERIFIER_nondet_int();

  retValue_acc = choice;
  return (retValue_acc);
  //return (retValue_acc);

}

void select_features()  { 

  {
  __SELECTED_FEATURE_Base = select_one();
  __SELECTED_FEATURE_Keys = select_one();
  __SELECTED_FEATURE_Encrypt = select_one();
  __SELECTED_FEATURE_AutoResponder = select_one();
  __SELECTED_FEATURE_AddressBook = select_one();
  __SELECTED_FEATURE_Sign = select_one();
  __SELECTED_FEATURE_Forward = select_one();
  __SELECTED_FEATURE_Verify = 1;
  __SELECTED_FEATURE_Decrypt = select_one();
  }
  return;
  
}

void select_helpers(void) { 
  
  __GUIDSL_ROOT_PRODUCTION = 1;
  return;
  
}


int valid_product() { 
  int retValue_acc ;
  int tmp ;

  {
  if ((__SELECTED_FEATURE_Encrypt==0) || (__SELECTED_FEATURE_Decrypt==1)) {
      if ((__SELECTED_FEATURE_Decrypt==0) || (__SELECTED_FEATURE_Encrypt==1)) {
          if ((__SELECTED_FEATURE_Encrypt==0) || (__SELECTED_FEATURE_Keys==1)) {
              if ((__SELECTED_FEATURE_Sign==0) || (__SELECTED_FEATURE_Verify==1)) {
                  if ((__SELECTED_FEATURE_Verify==0) || (__SELECTED_FEATURE_Sign==1)) {
                      if ((__SELECTED_FEATURE_Sign==0) || (__SELECTED_FEATURE_Keys==1)) {
                          if (__SELECTED_FEATURE_Base==1) {
                            tmp = 1;
                          } else {
                            tmp = 0;
                          }
                        } else {
                          tmp = 0;
                        }
                      } else {
                          tmp = 0;
                        }
                    } else {
                      tmp = 0;
                    }
                  } else {
                  tmp = 0;
                     }
                  } else {
              			tmp = 0;
            		}
          			} else {
          				tmp = 0;
        			}
      }

  retValue_acc = tmp;
  return (retValue_acc);
  //return (retValue_acc);
}


// *** IMPLEMENTING SETUP ***  //

#pragma merger(0,"ClientLib.i","")

int __ste_Client_counter  =    0;
int initClient() { 
  int retValue_acc;

  if (__ste_Client_counter < 3) {
    __ste_Client_counter = __ste_Client_counter + 1;
    retValue_acc = __ste_Client_counter;
    //return (retValue_acc);
  } else {
    retValue_acc = -1;
    //return (retValue_acc);
  }
  return (retValue_acc);

}

char __ste_client_name0 = 0;
char __ste_client_name1 = 0;
char __ste_client_name2 = 0;
char getClientName(int handle ) { 
  char retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_name0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_name1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_name2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}
void setClientName(int handle , char value ) { 

  if (handle == 1) {
    __ste_client_name0 = value;
  } else {
    if (handle == 2) {
      __ste_client_name1 = value;
    } else {
      if (handle == 3) {
        __ste_client_name2 = value;
      } else {

      }
    }
  }
  return;

}

int __ste_client_outbuffer0  =    0;
int __ste_client_outbuffer1  =    0;
int __ste_client_outbuffer2  =    0;
int __ste_client_outbuffer3  =    0;
int getClientOutbuffer(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_outbuffer0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_outbuffer1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_outbuffer2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientOutbuffer(int handle , int value ) { 

  if (handle == 1) {
    __ste_client_outbuffer0 = value;
  } else {
    if (handle == 2) {
      __ste_client_outbuffer1 = value;
    } else {
      if (handle == 3) {
        __ste_client_outbuffer2 = value;
      } else {

      }
    }
  }
  return;

}

int __ste_ClientAddressBook_size0  =    0;
int __ste_ClientAddressBook_size1  =    0;
int __ste_ClientAddressBook_size2  =    0;
int getClientAddressBookSize(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_ClientAddressBook_size0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_ClientAddressBook_size1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_ClientAddressBook_size2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);
	
}
void setClientAddressBookSize(int handle , int value ) { 

  if (handle == 1) {
    __ste_ClientAddressBook_size0 = value;
  } else {
    if (handle == 2) {
      __ste_ClientAddressBook_size1 = value;
    } else {
      if (handle == 3) {
        __ste_ClientAddressBook_size2 = value;
      } else {

      }
    }
  }
  return;

}

int createClientAddressBookEntry(int handle ) { 
  int retValue_acc ;
  int size ;
  int tmp ;
  int __cil_tmp5 ;

  
  tmp = getClientAddressBookSize(handle);
  size = tmp;
  
  if (size < 3) {
    
    __cil_tmp5 = size + 1;
    setClientAddressBookSize(handle, __cil_tmp5);
    retValue_acc = size + 1;
    
    //return (retValue_acc);
  } else {
    retValue_acc = -1;
    //return (retValue_acc);
  }
  return (retValue_acc);

}

int __ste_Client_AddressBook0_Alias0  =    0;
int __ste_Client_AddressBook0_Alias1  =    0;
int __ste_Client_AddressBook0_Alias2  =    0;
int __ste_Client_AddressBook1_Alias0  =    0;
int __ste_Client_AddressBook1_Alias1  =    0;
int __ste_Client_AddressBook1_Alias2  =    0;
int __ste_Client_AddressBook2_Alias0  =    0;
int __ste_Client_AddressBook2_Alias1  =    0;
int __ste_Client_AddressBook2_Alias2  =    0;
int getClientAddressBookAlias(int handle , int index ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (index == 0) {
      retValue_acc = __ste_Client_AddressBook0_Alias0;
      //return (retValue_acc);
    } else {
      if (index == 1) {
        retValue_acc = __ste_Client_AddressBook0_Alias1;
        //return (retValue_acc);
      } else {
        if (index == 2) {
          retValue_acc = __ste_Client_AddressBook0_Alias2;
          //return (retValue_acc);
        } else {
          retValue_acc = 0;
          //return (retValue_acc);
        }
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        retValue_acc = __ste_Client_AddressBook1_Alias0;
        //return (retValue_acc);
      } else {
        if (index == 1) {
          retValue_acc = __ste_Client_AddressBook1_Alias1;
          //return (retValue_acc);
        } else {
          if (index == 2) {
            retValue_acc = __ste_Client_AddressBook1_Alias2;
            //return (retValue_acc);
          } else {
            retValue_acc = 0;
            //return (retValue_acc);
          }
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          retValue_acc = __ste_Client_AddressBook2_Alias0;
          //return (retValue_acc);
        } else {
          if (index == 1) {
            retValue_acc = __ste_Client_AddressBook2_Alias1;
            //return (retValue_acc);
          } else {
            if (index == 2) {
              retValue_acc = __ste_Client_AddressBook2_Alias2;
              //return (retValue_acc);
            } else {
              retValue_acc = 0;
              //return (retValue_acc);
            }
          }
        }
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

int findClientAddressBookAlias(int handle , int userid ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (userid == __ste_Client_AddressBook0_Alias0) {
      retValue_acc = 0;
      //return (retValue_acc);
    } else {
      if (userid == __ste_Client_AddressBook0_Alias1) {
        retValue_acc = 1;
        //return (retValue_acc);
      } else {
        if (userid == __ste_Client_AddressBook0_Alias2) {
          retValue_acc = 2;
          //return (retValue_acc);
        } else {
          retValue_acc = -1;
          //return (retValue_acc);
        }
      }
    }
  } else {
    if (handle == 2) {
      if (userid == __ste_Client_AddressBook1_Alias0) {
        retValue_acc = 0;
        //return (retValue_acc);
      } else {
        if (userid == __ste_Client_AddressBook1_Alias1) {
          retValue_acc = 1;
          //return (retValue_acc);
        } else {
          if (userid == __ste_Client_AddressBook1_Alias2) {
            retValue_acc = 2;
            //return (retValue_acc);
          } else {
            retValue_acc = -1;
            //return (retValue_acc);
          }
        }
      }
    } else {
      if (handle == 3) {
        if (userid == __ste_Client_AddressBook2_Alias0) {
          retValue_acc = 0;
          //return (retValue_acc);
        } else {
          if (userid == __ste_Client_AddressBook2_Alias1) {
            retValue_acc = 1;
            //return (retValue_acc);
          } else {
            if (userid == __ste_Client_AddressBook2_Alias2) {
              retValue_acc = 2;
              //return (retValue_acc);
            } else {
              retValue_acc = -1;
              //return (retValue_acc);
            }
          }
        }
      } else {
        retValue_acc = -1;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}
	
void setClientAddressBookAlias(int handle , int index , int value ) { 

  if (handle == 1) {
    if (index == 0) {
      __ste_Client_AddressBook0_Alias0 = value;
    } else {
      if (index == 1) {
        __ste_Client_AddressBook0_Alias1 = value;
      } else {
        if (index == 2) {
          __ste_Client_AddressBook0_Alias2 = value;
        } else {

        }
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        __ste_Client_AddressBook1_Alias0 = value;
      } else {
        if (index == 1) {
          __ste_Client_AddressBook1_Alias1 = value;
        } else {
          if (index == 2) {
            __ste_Client_AddressBook1_Alias2 = value;
          } else {

          }
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          __ste_Client_AddressBook2_Alias0 = value;
        } else {
          if (index == 1) {
            __ste_Client_AddressBook2_Alias1 = value;
          } else {
            if (index == 2) {
              __ste_Client_AddressBook2_Alias2 = value;
            } else {

            }
          }
        }
      } else {

      }
    }
  }
  return;

}

int __ste_Client_AddressBook0_Address0  =    0;
int __ste_Client_AddressBook0_Address1  =    0;
int __ste_Client_AddressBook0_Address2  =    0;
int __ste_Client_AddressBook1_Address0  =    0;
int __ste_Client_AddressBook1_Address1  =    0;
int __ste_Client_AddressBook1_Address2  =    0;
int __ste_Client_AddressBook2_Address0  =    0;
int __ste_Client_AddressBook2_Address1  =    0;
int __ste_Client_AddressBook2_Address2  =    0;
int getClientAddressBookAddress(int handle , int index ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (index == 0) {
      retValue_acc = __ste_Client_AddressBook0_Address0;
      //return (retValue_acc);
    } else {
      if (index == 1) {
        retValue_acc = __ste_Client_AddressBook0_Address1;
        //return (retValue_acc);
      } else {
        if (index == 2) {
          retValue_acc = __ste_Client_AddressBook0_Address2;
          //return (retValue_acc);
        } else {
          retValue_acc = 0;
          //return (retValue_acc);
        }
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        retValue_acc = __ste_Client_AddressBook1_Address0;
        //return (retValue_acc);
      } else {
        if (index == 1) {
          retValue_acc = __ste_Client_AddressBook1_Address1;
          //return (retValue_acc);
        } else {
          if (index == 2) {
            retValue_acc = __ste_Client_AddressBook1_Address2;
            //return (retValue_acc);
          } else {
            retValue_acc = 0;
            //return (retValue_acc);
          }
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          retValue_acc = __ste_Client_AddressBook2_Address0;
          //return (retValue_acc);
        } else {
          if (index == 1) {
            retValue_acc = __ste_Client_AddressBook2_Address1;
            //return (retValue_acc);
          } else {
            if (index == 2) {
              retValue_acc = __ste_Client_AddressBook2_Address2;
              //return (retValue_acc);
            } else {
              retValue_acc = 0;
              //return (retValue_acc);
            }
          }
        }
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}
	
void setClientAddressBookAddress(int handle , int index , int value ) { 

  if (handle == 1) {
    if (index == 0) {
      __ste_Client_AddressBook0_Address0 = value;
    } else {
      if (index == 1) {
        __ste_Client_AddressBook0_Address1 = value;
      } else {
        if (index == 2) {
          __ste_Client_AddressBook0_Address2 = value;
        } else {

        }
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        __ste_Client_AddressBook1_Address0 = value;
      } else {
        if (index == 1) {
          __ste_Client_AddressBook1_Address1 = value;
        } else {
          if (index == 2) {
            __ste_Client_AddressBook1_Address2 = value;
          } else {

          }
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          __ste_Client_AddressBook2_Address0 = value;
        } else {
          if (index == 1) {
            __ste_Client_AddressBook2_Address1 = value;
          } else {
            if (index == 2) {
              __ste_Client_AddressBook2_Address2 = value;
            } else {

            }
          }
        }
      } else {

      }
    }
  }
  return;
	  
}

int __ste_client_autoResponse0  =    0;
int __ste_client_autoResponse1  =    0;
int __ste_client_autoResponse2  =    0;
int getClientAutoResponse(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_autoResponse0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_autoResponse1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_autoResponse2;
        //return (retValue_acc);
      } else {
        retValue_acc = -1;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientAutoResponse(int handle , int value ) { 

  if (handle == 1) {
    __ste_client_autoResponse0 = value;
  } else {
    if (handle == 2) {
      __ste_client_autoResponse1 = value;
    } else {
      if (handle == 3) {
        __ste_client_autoResponse2 = value;
      } else {

      }
    }
  }
  return;

}

int __ste_client_privateKey0  =    0;
int __ste_client_privateKey1  =    0;
int __ste_client_privateKey2  =    0;
int getClientPrivateKey(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_privateKey0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_privateKey1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_privateKey2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);
}
void setClientPrivateKey(int handle , int value ) { 

  if (handle == 1) {
    __ste_client_privateKey0 = value;
  } else {
    if (handle == 2) {
      __ste_client_privateKey1 = value;
    } else {
      if (handle == 3) {
        __ste_client_privateKey2 = value;
      } else {

      }
    }
  }
  return;
}

int __ste_ClientKeyring_size0  =    0;
int __ste_ClientKeyring_size1  =    0;
int __ste_ClientKeyring_size2  =    0;
int getClientKeyringSize(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_ClientKeyring_size0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_ClientKeyring_size1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_ClientKeyring_size2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientKeyringSize(int handle , int value ) { 

  if (handle == 1) {
    __ste_ClientKeyring_size0 = value;
  } else {
    if (handle == 2) {
      __ste_ClientKeyring_size1 = value;
    } else {
      if (handle == 3) {
        __ste_ClientKeyring_size2 = value;
      } else {

      }
    }
  }
  return;

}

int createClientKeyringEntry(int handle ) { 
  int retValue_acc ;
  int size ;
  int tmp ;
  int __cil_tmp5 ;

  
  tmp = getClientKeyringSize(handle);
  size = tmp;
  
  if (size < 2) {
    
    __cil_tmp5 = size + 1;
    setClientKeyringSize(handle, __cil_tmp5);
    retValue_acc = size + 1;
    
    //return (retValue_acc);
  } else {
    retValue_acc = -1;
    //return (retValue_acc);
  }
  return (retValue_acc);

}

int __ste_Client_Keyring0_User0  =    0;
int __ste_Client_Keyring0_User1  =    0;
int __ste_Client_Keyring0_User2  =    0;
int __ste_Client_Keyring1_User0  =    0;
int __ste_Client_Keyring1_User1  =    0;
int __ste_Client_Keyring1_User2  =    0;
int __ste_Client_Keyring2_User0  =    0;
int __ste_Client_Keyring2_User1  =    0;
int __ste_Client_Keyring2_User2  =    0;
int getClientKeyringUser(int handle , int index ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (index == 0) {
      retValue_acc = __ste_Client_Keyring0_User0;
      //return (retValue_acc);
    } else {
      if (index == 1) {
        retValue_acc = __ste_Client_Keyring0_User1;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        retValue_acc = __ste_Client_Keyring1_User0;
        //return (retValue_acc);
      } else {
        if (index == 1) {
          retValue_acc = __ste_Client_Keyring1_User1;
          //return (retValue_acc);
        } else {
          retValue_acc = 0;
          //return (retValue_acc);
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          retValue_acc = __ste_Client_Keyring2_User0;
          //return (retValue_acc);
        } else {
          if (index == 1) {
            retValue_acc = __ste_Client_Keyring2_User1;
            //return (retValue_acc);
          } else {
            retValue_acc = 0;
            //return (retValue_acc);
          }
        }
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientKeyringUser(int handle , int index , int value ) { 

  if (handle == 1) {
    if (index == 0) {
      __ste_Client_Keyring0_User0 = value;
    } else {
      if (index == 1) {
        __ste_Client_Keyring0_User1 = value;
      } else {

      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        __ste_Client_Keyring1_User0 = value;
      } else {
        if (index == 1) {
          __ste_Client_Keyring1_User1 = value;
        } else {

        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          __ste_Client_Keyring2_User0 = value;
        } else {
          if (index == 1) {
            __ste_Client_Keyring2_User1 = value;
          } else {

          }
        }
      } else {

      }
    }
  }
  return;

}

int __ste_Client_Keyring0_PublicKey0  =    0;
int __ste_Client_Keyring0_PublicKey1  =    0;
int __ste_Client_Keyring0_PublicKey2  =    0;
int __ste_Client_Keyring1_PublicKey0  =    0;
int __ste_Client_Keyring1_PublicKey1  =    0;
int __ste_Client_Keyring1_PublicKey2  =    0;
int __ste_Client_Keyring2_PublicKey0  =    0;
int __ste_Client_Keyring2_PublicKey1  =    0;
int __ste_Client_Keyring2_PublicKey2  =    0;
int getClientKeyringPublicKey(int handle , int index ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (index == 0) {
      retValue_acc = __ste_Client_Keyring0_PublicKey0;
      //return (retValue_acc);
    } else {
      if (index == 1) {
        retValue_acc = __ste_Client_Keyring0_PublicKey1;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        retValue_acc = __ste_Client_Keyring1_PublicKey0;
        //return (retValue_acc);
      } else {
        if (index == 1) {
          retValue_acc = __ste_Client_Keyring1_PublicKey1;
          //return (retValue_acc);
        } else {
          retValue_acc = 0;
          //return (retValue_acc);
        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          retValue_acc = __ste_Client_Keyring2_PublicKey0;
          //return (retValue_acc);
        } else {
          if (index == 1) {
            retValue_acc = __ste_Client_Keyring2_PublicKey1;
            //return (retValue_acc);
          } else {
            retValue_acc = 0;
            //return (retValue_acc);
          }
        }
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

int findPublicKey(int handle , int userid ) { 
  int retValue_acc ;

  if (handle == 1) {
    if (userid == __ste_Client_Keyring0_User0) {
      retValue_acc = __ste_Client_Keyring0_PublicKey0;
      //return (retValue_acc);
    } else {
      if (userid == __ste_Client_Keyring0_User1) {
        retValue_acc = __ste_Client_Keyring0_PublicKey1;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  } else {
    if (handle == 2) {
      if (userid == __ste_Client_Keyring1_User0) {
        retValue_acc = __ste_Client_Keyring1_PublicKey0;
        //return (retValue_acc);
      } else {
        if (userid == __ste_Client_Keyring1_User1) {
          retValue_acc = __ste_Client_Keyring1_PublicKey1;
          //return (retValue_acc);
        } else {
          retValue_acc = 0;
          //return (retValue_acc);
        }
      }
    } else {
      if (handle == 3) {
        if (userid == __ste_Client_Keyring2_User0) {
          retValue_acc = __ste_Client_Keyring2_PublicKey0;
          //return (retValue_acc);
        } else {
          if (userid == __ste_Client_Keyring2_User1) {
            retValue_acc = __ste_Client_Keyring2_PublicKey1;
            //return (retValue_acc);
          } else {
            retValue_acc = 0;
            //return (retValue_acc);
          }
        }
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientKeyringPublicKey(int handle , int index , int value ) { 

  if (handle == 1) {
    if (index == 0) {
      __ste_Client_Keyring0_PublicKey0 = value;
    } else {
      if (index == 1) {
        __ste_Client_Keyring0_PublicKey1 = value;
      } else {

      }
    }
  } else {
    if (handle == 2) {
      if (index == 0) {
        __ste_Client_Keyring1_PublicKey0 = value;
      } else {
        if (index == 1) {
          __ste_Client_Keyring1_PublicKey1 = value;
        } else {

        }
      }
    } else {
      if (handle == 3) {
        if (index == 0) {
          __ste_Client_Keyring2_PublicKey0 = value;
        } else {
          if (index == 1) {
            __ste_Client_Keyring2_PublicKey1 = value;
          } else {

          }
        }
      } else {

      }
    }
  }
  return;

}

int __ste_client_forwardReceiver0  =    0;
int __ste_client_forwardReceiver1  =    0;
int __ste_client_forwardReceiver2  =    0;
int __ste_client_forwardReceiver3  =    0;
int getClientForwardReceiver(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_forwardReceiver0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_forwardReceiver1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_forwardReceiver2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);

}

void setClientForwardReceiver(int handle , int value ) { 

  if (handle == 1) {
    __ste_client_forwardReceiver0 = value;
  } else {
    if (handle == 2) {
      __ste_client_forwardReceiver1 = value;
    } else {
      if (handle == 3) {
        __ste_client_forwardReceiver2 = value;
      } else {

      }
    }
  }
  return;

}



int __ste_client_idCounter0  =    0;
int __ste_client_idCounter1  =    0;
int __ste_client_idCounter2  =    0;
int getClientId(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_client_idCounter0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_client_idCounter1;
      //return (retValue_acc);
    } else {
      if (handle == 3) {
        retValue_acc = __ste_client_idCounter2;
        //return (retValue_acc);
      } else {
        retValue_acc = 0;
        //return (retValue_acc);
      }
    }
  }
  return (retValue_acc);
}

void setClientId(int handle , int value ) { 

  if (handle == 1) {
    __ste_client_idCounter0 = value;
  } else {
    if (handle == 2) {
      __ste_client_idCounter1 = value;
    } else {
      if (handle == 3) {
        __ste_client_idCounter2 = value;
      } else {

      }
    }
  }
  return;
}



// *** EmailLib  ***

#pragma merger(0,"EmailLib.i","")

int __ste_Email_counter  =    0;
int initEmail() { 
  int retValue_acc ;

  if (__ste_Email_counter < 2) {
    __ste_Email_counter = __ste_Email_counter + 1;
    retValue_acc = __ste_Email_counter;
    //return (retValue_acc);
  } else {
    retValue_acc = -1;
    //return (retValue_acc);
  }
  return (retValue_acc);

}

int __ste_email_id0  =    0;
int __ste_email_id1  =    0;
int getEmailId(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_id0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_id1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailId(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_id0 = value;
  } else {
    if (handle == 2) {
      __ste_email_id1 = value;
    } else {

    }
  }
  return;
}

int __ste_email_from0  =    0;
int __ste_email_from1  =    0;
int getEmailFrom(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_from0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_from1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailFrom(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_from0 = value;
  } else {
    if (handle == 2) {
      __ste_email_from1 = value;
    } else {

    }
  }
  return;
	
}

int __ste_email_to0  =    0;
int __ste_email_to1  =    0;
int getEmailTo(int handle) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_to0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_to1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  //assert (true);
  return (retValue_acc);

}

void setEmailTo(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_to0 = value;
  } else {
    if (handle == 2) {
      __ste_email_to1 = value;
    } else {

    }
  }
  return;
}

char __ste_email_subject0  ;
char __ste_email_subject1  ;
char getEmailSubject(int handle ) { 
  char retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_subject0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_subject1;
      //return (retValue_acc);
    } else {

      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);
	
}

void setEmailSubject(int handle , char value ) { 

  if (handle == 1) {
    __ste_email_subject0 = value;
  } else {
    if (handle == 2) {
      __ste_email_subject1 = value;
    } else {

    }
  }
  return;

}

char __ste_email_body0  = 0;
char __ste_email_body1  = 0;
char getEmailBody(int handle ) { 
  char retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_body0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_body1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailBody(int handle , char value ) { 

  if (handle == 1) {
    __ste_email_body0 = value;
  } else {
    if (handle == 2) {
      __ste_email_body1 = value;
    } else {

    }
  }
  return;

}

int __ste_email_isEncrypted0  =    0;
int __ste_email_isEncrypted1  =    0;
int isEncrypted(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_isEncrypted0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_isEncrypted1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailIsEncrypted(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_isEncrypted0 = value;
  } else {
    if (handle == 2) {
      __ste_email_isEncrypted1 = value;
    } else {

    }
  }
  return;

}

int __ste_email_encryptionKey0  =    0;
int __ste_email_encryptionKey1  =    0;
int getEmailEncryptionKey(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_encryptionKey0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_encryptionKey1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailEncryptionKey(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_encryptionKey0 = value;
  } else {
    if (handle == 2) {
      __ste_email_encryptionKey1 = value;
    } else {

    }
  }
  return;
	  
}

int __ste_email_isSigned0  =    0;
int __ste_email_isSigned1  =    0;
int isSigned(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_isSigned0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_isSigned1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailIsSigned(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_isSigned0 = value;
  } else {
    if (handle == 2) {
      __ste_email_isSigned1 = value;
    } else {

    }
  }
  return;

}

int __ste_email_signKey0  =    0;
int __ste_email_signKey1  =    0;
int getEmailSignKey(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_signKey0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_signKey1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailSignKey(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_signKey0 = value;
  } else {
    if (handle == 2) {
      __ste_email_signKey1 = value;
    } else {

    }
  }
  return;

}

int __ste_email_isSignatureVerified0  ;
int __ste_email_isSignatureVerified1  ;
int isVerified(int handle ) { 
  int retValue_acc ;

  if (handle == 1) {
    retValue_acc = __ste_email_isSignatureVerified0;
    //return (retValue_acc);
  } else {
    if (handle == 2) {
      retValue_acc = __ste_email_isSignatureVerified1;
      //return (retValue_acc);
    } else {
      retValue_acc = 0;
      //return (retValue_acc);
    }
  }
  return (retValue_acc);

}

void setEmailIsSignatureVerified(int handle , int value ) { 

  if (handle == 1) {
    __ste_email_isSignatureVerified0 = value;
  } else {
    if (handle == 2) {
      __ste_email_isSignatureVerified1 = value;
    } else {

    }
  }
  return;

}

// *** Client  ***

#pragma merger(0,"Client.i","")

int isReadable(int msg ) ;
int createEmail(int from , int to ) ;
void incoming(int client , int msg ) ;
void mail(int client , int msg ) ;
void sendToAddressBook(int client , int msg ) ;
void sign(int client , int msg ) ;
void autoRespond(int client , int msg ) ;
void forward(int client , int msg ) ;
void verify(int client , int msg ) ;
int isKeyPairValid(int publicKey , int privateKey ) ;
int queue_empty  =    1;
int queued_message  ;
int queued_client  ;

void queue(int client , int msg ) { 

  queue_empty = 0;
  queued_message = msg;
  queued_client = client;
  return;

}


#pragma merger(0,"DecryptForward_spec.i","")
void __utac_acc__DecryptForward_spec__1(int msg ) 
{ int tmp ;

  puts("before forward\n");
  tmp = isReadable(msg);
 
  assert (tmp == 1); 
 
  return;

}


void forward(int client , int msg ) { 

  __utac_acc__DecryptForward_spec__1(msg);
  puts("Forwarding message.\n");
  //printMail(msg);
  queue(client, msg);
  
  return;

}


void verify(int client , int msg ) { 
  int tmp ;
  int tmp___0 ;
  int pubkey ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;



  tmp = isReadable(msg);
  if (tmp==1) {
    tmp___0 = isSigned(msg);
    if (tmp___0==1) {

  		tmp___1 = getEmailFrom(msg);
  		tmp___2 = findPublicKey(client, tmp___1);
  		pubkey = tmp___2;
  
  		if (pubkey==1) {
    		tmp___3 = getEmailSignKey(msg);
    		tmp___4 = isKeyPairValid(tmp___3, pubkey);
 
    		if (tmp___4==1) {
      
      			setEmailIsSignatureVerified(msg, 1);
      
    		} 
  		}
	}
  }

  return;

}

void autoRespond(int client , int msg ) 
{ 
  int sender ;
  int tmp ;

  puts("sending autoresponse\n");
  tmp = getEmailFrom(msg);
  sender = tmp;
  setEmailTo(msg, sender);
  queue(client, msg);
  
  return;

}


void deliver(int client , int msg ) { 

  puts("mail delivered\n");
  return;

}

void incoming__before__AutoResponder(int client , int msg ) { 
  //assert (true);
  {
  deliver(client, msg);
  }
  return;

}

void incoming__role__AutoResponder(int client , int msg ) { 
   int tmp ;

  incoming__before__AutoResponder(client, msg);
  tmp = getClientAutoResponse(client);
  
  if (tmp==1) {
    {
    autoRespond(client, msg);
    }
  } else {

  } 
  return;

}

void incoming__before__Forward(int client , int msg ) { 

  if (__SELECTED_FEATURE_AutoResponder==1) {
    
    incoming__role__AutoResponder(client, msg);
    
    //return;
  } else {
    
    incoming__before__AutoResponder(client, msg);
    
    //return;
  }
  return;
}
	
void incoming__role__Forward(int client , int msg ) { 
  int fwreceiver ;
  int tmp ;

  
  incoming__before__Forward(client, msg);
  tmp = getClientForwardReceiver(client);
  fwreceiver = tmp;
  
  if (fwreceiver==1) {
    {
    setEmailTo(msg, fwreceiver);
    forward(client, msg);
    }
  } else {

  } 
  return;

}

void incoming__before__Verify(int client , int msg ) { 

  if (__SELECTED_FEATURE_Forward==1) {
    
    incoming__role__Forward(client, msg);
    
    //return;
  } else {
    
    incoming__before__Forward(client, msg);
    
    //return;
  }
  return;
}
	
void incoming__role__Verify(int client , int msg ) { 

  {
  verify(client, msg);
  incoming__before__Verify(client, msg);
  }
  return;

}	

void incoming__before__Decrypt(int client , int msg ) { 

  if (__SELECTED_FEATURE_Verify==1) {
    
    incoming__role__Verify(client, msg);
    
    //return;
  } else {
    
    incoming__before__Verify(client, msg);
    
    //return;
  }
  return;

}
	
void incoming__role__Decrypt(int client , int msg ) { 
  int privkey ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;

  {
  tmp = getClientPrivateKey(client);
  privkey = tmp;
  }
  if (privkey==1) {
    {
    tmp___0 = isEncrypted(msg);
    }
    if (tmp___0==1) {
      {
      tmp___1 = getEmailEncryptionKey(msg);
      tmp___2 = isKeyPairValid(tmp___1, privkey);
      }
      if (tmp___2==1) {
        {
        setEmailIsEncrypted(msg, 0);
        setEmailEncryptionKey(msg, 0);
        }
      } else {

      }
    } else {

    }
  } else {

  }
  
  incoming__before__Decrypt(client, msg);
  
  return;

}	

void incoming(int client , int msg ) { 
	

  if (__SELECTED_FEATURE_Decrypt==1) {
    
    incoming__role__Decrypt(client, msg);
    
  } else {
    
    incoming__before__Decrypt(client, msg);
    
  }
  return;
	
}	

void mail(int client , int msg ) { 
  int tmp ;
  //assert (true); 
  
  //__utac_acc__AddressBookEncrypt_spec__1(client, msg);
  //puts("mail sent");
  tmp = getEmailTo(msg);
  //assert (true); 
  incoming(tmp, msg);
	
  return;

}


void outgoing__before__Encrypt(int client , int msg ) { 
   int tmp ;

  {
  tmp = getClientId(client);
  setEmailFrom(msg, tmp);
  mail(client, msg);
  }
  return;

}

void outgoing__role__Encrypt(int client , int msg ) { 
  int receiver ;
  int tmp ;
  int pubkey ;
  int tmp___0 ;

  {
  tmp = getEmailTo(msg);
  receiver = tmp;
  tmp___0 = findPublicKey(client, receiver);
  pubkey = tmp___0;
  }
  if (pubkey==1) {
    {
    setEmailEncryptionKey(msg, pubkey);
    setEmailIsEncrypted(msg, 1);
    }
  } else {

  }
  {
  outgoing__before__Encrypt(client, msg);
  }
  return;

}

void outgoing__before__AddressBook(int client , int msg ) { 

  if (__SELECTED_FEATURE_Encrypt==1) {
    
    outgoing__role__Encrypt(client, msg);
    
    //return;
  } else {
    
    outgoing__before__Encrypt(client, msg);
    
    //return;
  }
  return;

}
	
void outgoing__role__AddressBook(int client , int msg ) { 
  int size ;
  int tmp ;
  int receiver ;
  int tmp___0 ;
  int second ;
  int tmp___1 ;
  int tmp___2 ;

  tmp = getClientAddressBookSize(client);
  size = tmp;

  if (size>0) {
    {
    sendToAddressBook(client, msg);
    puts("sending to alias in address book\n");
    tmp___0 = getEmailTo(msg);
    receiver = tmp___0;
    puts("sending to second receipient\n");
    tmp___1 = getClientAddressBookAddress(client, 1);
    second = tmp___1;
    setEmailTo(msg, second);
    outgoing__before__AddressBook(client, msg);
    tmp___2 = getClientAddressBookAddress(client, 0);
    setEmailTo(msg, tmp___2);
    outgoing__before__AddressBook(client, msg);  
    }
  } else {
    {
    outgoing__before__AddressBook(client, msg);
    }
  } 
  return;

}

void outgoing__before__Sign(int client , int msg ) { 

  if (__SELECTED_FEATURE_AddressBook==1) {
    outgoing__role__AddressBook(client, msg);
    //return;
  } else {
    outgoing__before__AddressBook(client, msg);
    //return;
  }
  return;	

}

void outgoing__role__Sign(int client , int msg ) { 

  {
  sign(client, msg);
  outgoing__before__Sign(client, msg);
  }
  return;

}

void outgoing(int client , int msg ) { 
   
  if (__SELECTED_FEATURE_Sign==1) {
    outgoing__role__Sign(client, msg);
    //return;
  } else {
    outgoing__before__Sign(client, msg);
    //return;
  }
  return;

}


int createClient(char name ) { 
  int retValue_acc ;
  int client ;
  int tmp ;

  {
  tmp = initClient();
  client = tmp;
  retValue_acc = client;
  }
  return (retValue_acc);

}	
	
void sendEmail(int sender , int receiver ) { 
  int email ;
  int tmp ;

  {
  tmp = createEmail(0, receiver);
  email = tmp;
  outgoing(sender, email);
  }
  return;
	
}	



int is_queue_empty() { 
  int retValue_acc ;

  retValue_acc = queue_empty;
  return (retValue_acc);

}

int get_queued_client() { 
  int retValue_acc ;

  retValue_acc = queued_client;
  return (retValue_acc);

}

int get_queued_email() { 
  int retValue_acc ;

  retValue_acc = queued_message;
  return (retValue_acc);

}

int isKeyPairValid(int publicKey , int privateKey ) { 
  int retValue_acc ;

  printf("keypair valid %d %d", publicKey, privateKey);

  if (publicKey==0) {
    retValue_acc = 0;
    //return (retValue_acc);
  } else {
    if (privateKey==0) {
      retValue_acc = 0;
      //return (retValue_acc);
    } else {
		retValue_acc = privateKey == publicKey;
    }
  }
  
  return (retValue_acc);

}

void generateKeyPair(int client , int seed ) { 

  setClientPrivateKey(client, seed);
  return;

}




/*void autoRespond(int client , int msg ) { 
  int sender ;
  int tmp ;

  puts("sending autoresponse\n");
  tmp = getEmailFrom(msg);
  sender = tmp;
  setEmailTo(msg, sender);
  queue(client, msg);
  
  return;

}  */

void sendToAddressBook(int client , int msg ) { 

  return;

}

void sign(int client , int msg ) { 
  int privkey ;
  int tmp ;

  tmp = getClientPrivateKey(client);
  privkey = tmp;

  if (privkey==0) {

  } else {
  	setEmailIsSigned(msg, 1);
  	setEmailSignKey(msg, privkey);
  }

  return;

}



#pragma merger(0,"Test.i","")
int bob  ;
int rjh  ;
int chuck  ;
void setup_bob__before__Keys(int bob___0 )  { 

  setClientId(bob___0, bob___0);

  return;
}

void setup_bob__role__Keys(int bob___0 ) { 

  setup_bob__before__Keys(bob___0);
  setClientPrivateKey(bob___0, 123);

  return;
}

void setup_bob(int bob___0 ) { 

  if (__SELECTED_FEATURE_Keys==1) {
    
    setup_bob__role__Keys(bob___0);
    
    //return;
  } else {
 
    setup_bob__before__Keys(bob___0);
    
    //return;
  }
  return;
}

void setup_rjh__before__Keys(int rjh___0 ) { 

  setClientId(rjh___0, rjh___0);
  return;
}

void setup_rjh__role__Keys(int rjh___0 ) { 

  setup_rjh__before__Keys(rjh___0);
  setClientPrivateKey(rjh___0, 456);
  
  return;
}

void setup_rjh(int rjh___0 ) { 

  if (__SELECTED_FEATURE_Keys==1) {
    
    setup_rjh__role__Keys(rjh___0);
    
    //return;
  } else {
    
    setup_rjh__before__Keys(rjh___0);
   
    //return;
  }
  return;
}

void setup_chuck__before__Keys(int chuck___0 )  { 

  setClientId(chuck___0, chuck___0);
  
  return;
}

void setup_chuck__role__Keys(int chuck___0 ) { 

  setup_chuck__before__Keys(chuck___0);
  setClientPrivateKey(chuck___0, 789);
  
  return;
}

void setup_chuck(int chuck___0 ) { 

  if (__SELECTED_FEATURE_Keys==1) {
    
    setup_chuck__role__Keys(chuck___0);
    
    //return;
  } else {
    
    setup_chuck__before__Keys(chuck___0);
    
    //return;
  }
  return; 
}

void bobToRjh()  { 
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;

  {
  puts("Please enter a subject and a message body.\n");
  sendEmail(bob, rjh);
  tmp___1 = is_queue_empty();
  }
  if (tmp___1==1) {

  } else {
    {
    tmp = get_queued_email();
    tmp___0 = get_queued_client();
    outgoing(tmp___0, tmp);
    }
  }
  return;

}

void rjhToBob() { 

  {
  puts("Please enter a subject and a message body.\n");
  sendEmail(rjh, bob);
  }
  return;

}

void setup()  { 
  char const __cil_tmp1 ;
  char const __cil_tmp2 ;
  char const __cil_tmp3 ;

  {
  bob = 1;
  setup_bob(bob);
  __cil_tmp1 = 98; //'b'; //(char const   * __restrict  )"bob: %d\n";
  printf(__cil_tmp1, bob);
  rjh = 2;
  setup_rjh(rjh);
  __cil_tmp2 = 114; //'r'; //(char const   * __restrict  )"rjh: %d\n";
  printf(__cil_tmp2, rjh);
  chuck = 3;
  setup_chuck(chuck);
  __cil_tmp3 = 99; //'c'; //(char const   * __restrict  )"chuck: %d\n";
  printf(__cil_tmp3, chuck);
  }
  return;
}

void bobKeyAdd() { 
  int tmp ;
  int tmp___0 ;

  createClientKeyringEntry(bob);
  setClientKeyringUser(bob, 0, 2);
  setClientKeyringPublicKey(bob, 0, 456);
  puts("bob added rjhs key");
  tmp = getClientKeyringUser(bob, 0);

  printf("%d\n", tmp);
  tmp___0 = getClientKeyringPublicKey(bob, 0);

  printf("%d\n", tmp___0);

  return;

}

void rjhKeyAdd() { 

  
  createClientKeyringEntry(rjh);
  setClientKeyringUser(rjh, 0, 1);
  setClientKeyringPublicKey(rjh, 0, 123);
  
  return;
	
}

void rjhKeyAddChuck() { 

  
  createClientKeyringEntry(rjh);
  setClientKeyringUser(rjh, 0, 3);
  setClientKeyringPublicKey(rjh, 0, 789);
  
  return;

}

void bobKeyAddChuck() { 

  createClientKeyringEntry(bob);
  setClientKeyringUser(bob, 1, 3);
  setClientKeyringPublicKey(bob, 1, 789);

  return;

}

void chuckKeyAdd() { 

  createClientKeyringEntry(chuck);
  setClientKeyringUser(chuck, 0, 1);
  setClientKeyringPublicKey(chuck, 0, 123);

  return;

}

void chuckKeyAddRjh() { 

  createClientKeyringEntry(chuck);
  setClientKeyringUser(chuck, 0, 2);
  setClientKeyringPublicKey(chuck, 0, 456);

  return;

}

void rjhDeletePrivateKey() { 

  setClientPrivateKey(rjh, 0);

  return;

}

void bobKeyChange() { 

  generateKeyPair(bob, 777);

  return;

}

void rjhKeyChange() { 

  generateKeyPair(rjh, 666);

  return;

}

void rjhSetAutoRespond() { 

  setClientAutoResponse(rjh, 1);
	
  return;

}

void bobSetAddressBook() { 

  setClientAddressBookSize(bob, 1);
  setClientAddressBookAlias(bob, 0, rjh);
  setClientAddressBookAddress(bob, 0, rjh);
  setClientAddressBookAddress(bob, 1, chuck);

  return;

}

void rjhEnableForwarding() { 

  setClientForwardReceiver(rjh, chuck);
  return;

}

// *** IMPLEMENTING TEST ***  //
void test(void) { 
  int op1 ;
  int op2 ;
  int op3 ;
  int op4 ;
  int op5 ;
  int op6 ;
  int op7 ;
  int op8 ;
  int op9 ;
  int op10 ;
  int op11 ;
  int splverifierCounter ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  int tmp___5 ;
  int tmp___6 ;
  int tmp___7 ;
  int tmp___8 ;
  int tmp___9 ;


  op1 = 0;
  op2 = 0;
  op3 = 0;
  op4 = 0;
  op5 = 0;
  op6 = 0;
  op7 = 0;
  op8 = 0;
  op9 = 0;
  op10 = 0;
  op11 = 0;
  splverifierCounter = 0;
  int guard=1; 
  while (guard==1) {
    //while_3_continue: /* CIL Label */ ;
    if (splverifierCounter >= 4) {
		  //bobToRjh(); 
		  guard=0; 
    } 
	else {
    splverifierCounter = splverifierCounter + 1;
	
	tmp___9 = [0,1]; //__VERIFIER_nondet_int();
    if ((op1==0) && (tmp___9==1)) {
      
        if (__SELECTED_FEATURE_Keys==1) {
          {
          bobKeyAdd();
          }
        } else {

        }
        op1 = 1;
 
    } else {
	  tmp___8 = [0,1]; // __VERIFIER_nondet_int();
      if ((op2==0) && (tmp___8==1))  {

          if (__SELECTED_FEATURE_AutoResponder==1) {
            {
            rjhSetAutoRespond();
            }
          } else {

          }
          op2 = 1;

      } else {
		tmp___7 = [0,1]; // __VERIFIER_nondet_int();
        if ((op3==0) && (tmp___7==1)) {

            if (__SELECTED_FEATURE_Keys==1) {
              {
              rjhDeletePrivateKey();
              }
            } else {

            }
            op3 = 1;

        } else {
		  tmp___6 = [0,1]; // __VERIFIER_nondet_int();
          if ((op4==0) && (tmp___6==1)) {

              if (__SELECTED_FEATURE_Keys==1) {
                {
                rjhKeyAdd();
                }
              } else {

              }
              op4 = 1;

          } else {
            tmp___5 = [0,1]; // __VERIFIER_nondet_int();
            if ((op5==0) && (tmp___5==1)) {

                if (__SELECTED_FEATURE_Keys==1) {
                  {
                  chuckKeyAddRjh();
                  }
                } else {

                }
                op5 = 1;

            } else {
              tmp___4 = [0,1]; // __VERIFIER_nondet_int(); 
              if ((op6==0) && (tmp___4==1)) {

                  if (__SELECTED_FEATURE_Forward==1) {
                    {
                    rjhEnableForwarding();
                    }
                  } else {

                  }
                  op6 = 1;

              } else {
                tmp___3 = [0,1]; // __VERIFIER_nondet_int(); 
                if ((op7==0) && (tmp___3==1))  {

                    if (__SELECTED_FEATURE_Keys==1) {
                      {
                      rjhKeyChange();
                      }
                    } else {

                    }
                    op7 = 1;

                } else {
                  tmp___2 = [0,1]; // __VERIFIER_nondet_int();
                  if ((op8==0) && (tmp___2==1)) {

                      if (__SELECTED_FEATURE_AddressBook==1) {
                        {
                        bobSetAddressBook();
                        }
                      } else {

                      }
                      op8 = 1;

                  } else {
                    tmp___1 = [0,1]; // __VERIFIER_nondet_int();
                    if ((op9==0) && (tmp___1==1)) {

                        if (__SELECTED_FEATURE_Keys==1) {
                          {
                          chuckKeyAdd();
                          }
                        } else {

                        }
                        op9 = 1;

                    } else {
                      tmp___0 = [0,1]; //__VERIFIER_nondet_int();
                      if ((op10==0) && (tmp___0==1)) {

                          if (__SELECTED_FEATURE_Keys==1) {
                            {
                            bobKeyChange();
                            }
                          } else {

                          }
                          op10 = 1;

                      } else {
                        tmp = [0,1]; // __VERIFIER_nondet_int();
                        if ((op11==0) && (tmp==1)) {

                            if (__SELECTED_FEATURE_Keys==1) {
                              {
                              chuckKeyAdd();
                              }
                            } else {

                            }
                            op11 = 1;

                        } else {
                          	//bobToRjh(); 
							guard=0; 
  		  					//return;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  }

  
  bobToRjh();
 
  return;
}


#pragma merger(0,"Email.i","")

int isReadable__before__Encrypt(int msg ) { 
  int retValue_acc ;

  retValue_acc = 1;
  return (retValue_acc);

}

int isReadable__role__Encrypt(int msg ) { 
  int retValue_acc ;
  int tmp ;

  tmp = isEncrypted(msg);
  
  if (tmp==1) {
    retValue_acc = 0;
    //return (retValue_acc);
  } else {
    
    retValue_acc = isReadable__before__Encrypt(msg);
    
    //return (retValue_acc);
  }
  return (retValue_acc);

}
int isReadable(int msg ) { 
  int retValue_acc ;

  if (__SELECTED_FEATURE_Encrypt==1) {
    retValue_acc = isReadable__role__Encrypt(msg);
    //return (retValue_acc);
  } else {
    retValue_acc = isReadable__before__Encrypt(msg);
    //return (retValue_acc);
  }
  return (retValue_acc);

}

int cloneEmail(int msg ) 
{ int retValue_acc ;

  retValue_acc = msg;
  return (retValue_acc);

}

int createEmail(int from , int to ) { 
  int retValue_acc ;
  int msg ;

  msg = 1;
  setEmailFrom(msg, from);
  setEmailTo(msg, to);
  retValue_acc = msg;
  return (retValue_acc);

}



	
/* *** MAIN *** */	


int main()  { 
  int retValue_acc ;
  int tmp ;

  select_helpers();
  select_features();
  tmp = valid_product();
  
  if (tmp==1) {
    setup();
    test();
  } else {

  } 
  return (retValue_acc);

}


/*  *** SPECIFICATION *** */



