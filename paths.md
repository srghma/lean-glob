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

| Path Type | Target | Example Path | Description |
| :--- | :--- | :--- | :--- |
| **Absolute** | **File** | `C:\Windows\System32\cmd.exe` | Points directly to the Command Prompt executable on the C: drive. |
| **Absolute** | **File** | `D:\Users\John\Documents\budget.xlsx` | Points to an Excel sheet in a user directory on the D: drive. |
| **Absolute** | **Directory** | `C:\Program Files\Java` | Points to the Java installation directory on the C: drive. |
| **Absolute** | **Directory** | `\\Server01\Shared\Reports` | A UNC (Universal Naming Convention) absolute path pointing to a shared network directory. |
| **Relative** | **File** | `settings.ini` | Points to an initialization file in the current working directory. |
| **Relative** | **File** | `.\config\database.db` | Points to a database file inside the `config` folder of the current directory. |
| **Relative** | **File** | `..\src\main.py` | Goes up to the parent directory, then into the `src` folder to find the script. |
| **Relative** | **Directory** | `assets\images` | Points to a directory relative to the current working directory. |
| **Relative** | **Directory** | `..` | Points to the parent directory of the current working directory. |
