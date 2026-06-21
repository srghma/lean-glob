### **Linux (POSIX)**

Linux and other Unix-like systems use forward slashes (`/`) as path separators, are case-sensitive, and use a single root directory (`/`) with no drive letters.

| Path Type | Target | Example Path | Description |
| :--- | :--- | :--- | :--- |
| **Absolute** | **File** | `/var/log/syslog` | Points directly to the system log file from the root directory. |
| **Absolute** | **File** | `/home/user/documents/report.pdf` | Points to a PDF file in a specific user's home directory. |
| **Absolute** | **Directory** | `/etc/nginx/conf.d` | Points to a directory containing Nginx configuration files. |
| **Absolute** | **Directory** | `/usr/local/bin` | Points to the system directory for locally installed binaries. |
| **Relative** | **File** | `config.json` | Points to a file in the current working directory. |
| **Relative** | **File** | `./scripts/deploy.sh` | Points to a script inside a subdirectory of the current folder. |
| **Relative** | **File** | `../logs/error.log` | Goes up one level to the parent directory, then down into the `logs` folder to find the file. |
| **Relative** | **Directory** | `projects/website` | Points to a directory relative to the current working directory. |
| **Relative** | **Directory** | `..` | Points to the parent directory of the current working directory. |

---

### **Windows**

Windows systems typically use backslashes (`\`) as path separators, are case-insensitive, and use drive letters (like `C:`, `D:`) to represent different storage volumes.

| Path Type | Target | Example Path |
| :--- | :--- | :--- |
| **Absolute** | **File** | `C:\Windows\System32\cmd.exe` |
| **Absolute** | **Directory** | `C:\Program Files\Java` |
| **Absolute (Mixed)** | **File** | `C:\Windows/System32\cmd.exe` |
| **Absolute (Forward)** | **Directory** | `C:/Program Files/Java` |
| **Absolute (UNC)** | **Directory** | `\\Server01\Shared\Reports` |
| **Absolute (Verbatim Disk)** | **File** | `\\?\C:\VeryLongPath\file.txt` |
| **Absolute (Verbatim UNC)** | **File** | `\\?\UNC\Server01\Shared\file.txt` |
| **Relative** | **File** | `settings.ini` |
| **Relative** | **File** | `.\config\database.db` |
| **Relative (Mixed)** | **File** | `.\config/database.db` |
| **Relative** | **File** | `..\src\main.py` |
| **Relative (Current Drive)** | **Directory** | `\Users\John\Documents` |
| **Relative (Drive-Relative)** | **File** | `D:Documents\budget.xlsx` |
| **Relative** | **Directory** | `assets\images` |
| **Relative** | **Directory** | `..` |
